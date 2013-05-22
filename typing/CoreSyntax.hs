module CoreSyntax where

import Localizing
import Classes
import Utils

import Data.Char
import Data.Map

---------------------------------
-- Representation of variables --

data Variable = 
  Var { uid :: Int,
        ext :: Extent }

instance Show Variable where
  show (Var { uid = n, ext = ex }) = show n ++ "@" ++ show ex

-----------------------
-- Exponential flags --

type Flag = Int

---------------------------------
-- Representation of Quipper's --
-- types                       --

data Type =
    TVar Int              -- Introduced in the core syntax
  | TUnit
  | TBool
  | TQBit
  | TCirc FType FType
  | TTensor FType FType
  | TArrow FType FType
  -- No ! type

data FType = FTyp Type Flag  -- The integer is a flag's unique id

---------------------------------
-- Representation of patterns  --

data Pattern =
    PUnit
  | PVar Variable
  | PPair Pattern Pattern
  | PConstraint Pattern FType

---------------------------------
-- Quipper's terms             --

data Expr =
    EUnit
  | EConstraint Expr FType
  | EVar Variable
  | EFun Pattern Expr
  | ELet Pattern Expr Expr
  | EApp Expr Expr
  | EBool Bool
  | EPair Expr Expr
  | EBox FType
  | EUnbox Expr
  | EIf Expr Expr Expr
  | ERev
  | ELocated Expr Extent
  deriving Show

-- Extract all the free type variables
extractVariables :: Type -> [Int]
------------------------------------
extractVariables (TVar x) = [x]
extractVariables (TTensor (FTyp t1 _) (FTyp t2 _)) = extractVariables t1 ++ extractVariables t2
extractVariables (TCirc (FTyp t1 _) (FTyp t2 _)) = extractVariables t1 ++ extractVariables t2
extractVariables (TArrow (FTyp t1 _) (FTyp t2 _)) = extractVariables t1 ++ extractVariables t2
extractVariables _ = []

-- Substitute type variable x by type a in type t
-- The flags are left untouched in the original type
subst :: Int -> Type -> FType -> FType
---------------------------------------
subst x a (FTyp (TVar y) f) | x == y = FTyp a f
                            | otherwise = FTyp (TVar y) f
subst x a (FTyp (TTensor t1 t2) f) = FTyp (TTensor (subst x a t1) (subst x a t2)) f
subst x a (FTyp (TCirc t1 t2) f) = FTyp (TCirc (subst x a t1) (subst x a t2)) f
subst x a (FTyp (TArrow t1 t2) f) = FTyp (TArrow (subst x a t1) (subst x a t2)) f
subst _ _ t = t

-- Apply all the substitutions defined by the map
substAll :: Map Int Type -> FType -> FType
-------------------------------------------
substAll sub (FTyp (TVar x) f) =
  case Data.Map.lookup x sub of
  Just t -> FTyp t f
  Nothing -> FTyp (TVar x) f
substAll sub (FTyp (TTensor t1 t2) f) = FTyp (TTensor (substAll sub t1) (substAll sub t2)) f
substAll sub (FTyp (TCirc t1 t2) f) = FTyp (TCirc (substAll sub t1) (substAll sub t2)) f
substAll sub (FTyp (TArrow t1 t2) f) = FTyp (TArrow (substAll sub t1) (substAll sub t2)) f
substAll _ t = t

-- Apply the substitution until the fixpoint is attained
appSubst :: Map Int Type -> FType -> FType
-------------------------------------------
appSubst sub t =
  let t' = substAll sub t in
  if t == t' then
    t
  else
    appSubst sub t'

-- Value identification
isValue :: Expr -> Bool
-----------------------
isValue (ELocated e _) = isValue e
isValue (EConstraint e _) = isValue e
isValue (EUnbox e) = isValue e
isValue (EPair e1 e2) = isValue e1 && isValue e2
isValue (EIf _ _ _) = False
isValue (EApp _ _) = False
isValue (ELet _ _ _) = False
isValue _ = True

-----------------------
-- Comparable things --

-- Eq instance declaration of types
-- The declaration takes into account the ismorphism : !! A = ! A
instance Eq Type where
  (==) (TVar x) (TVar y) = x == y
  (==) TUnit TUnit = True
  (==) TBool TBool = True
  (==) TQBit TQBit = True
  (==) (TCirc t1 t2) (TCirc u1 u2) = (t1 == u1) && (t2 == u2)
  (==) (TTensor t1 t2) (TTensor u1 u2) = (t1 == u1) && (t2 == u2)
  (==) (TArrow t1 t2) (TArrow u1 u2) = (t1 == u1) && (t2 == u2)
  (==) _ _ = False

instance Eq FType where
  (==) (FTyp t _) (FTyp u _) = t == u

--------------------
-- Located things --

instance Located Expr where
  locate (ELocated e ex) _ = ELocated e ex
  locate e ex = ELocated e ex
  location (ELocated _ ex) = Just ex
  location _ = Nothing
  locate_opt e Nothing = e
  locate_opt e (Just ex) = locate e ex

-------------------
-- Atomic things --

instance Atomic Type where
  is_atomic (TTensor _ _) = False
  is_atomic (TArrow _ _) = False
  is_atomic _ = True

instance Atomic Expr where
  is_atomic (ELocated e _) = is_atomic e
  is_atomic (EApp _ _) = False
  is_atomic (EIf _ _ _) = False
  is_atomic (EFun _ _) = False
  is_atomic _ = True

--------------
-- Printing --

instance Show Type where
  show (TVar x) = "X" ++ (subscript $ show x)
  show TUnit = "()"
  show TBool = "bool"
  show TQBit = "qbit"
  show (TCirc t u) = "circ (" ++ show t ++ ", " ++ show u ++ ")"
  show (TTensor t u) = show t ++ " * " ++ show u
  show (TArrow t u) = show t ++ " -> " ++ show u

instance Show FType where
  show (FTyp t f) =
    "!" ++ (superscript $ show f) ++ (if is_atomic t then show t else "(" ++ show t ++ ")")

instance Show Pattern where
  show (PVar x) = "x" ++ (subscript $ show $ uid x)
  show (PPair p1 p2) = "<" ++ show p1 ++ ", " ++ show p2 ++ ">"
  show PUnit = "<>"
  show (PConstraint p t) = "(" ++ show p ++ " : " ++ show t ++ ")"

---------------------
-- Pretty printing --

-- Second argument is indentation level
pshowExpr :: Expr -> String -> String
-------------------------------------
pshowExpr EUnit _ = "<>"
pshowExpr (EConstraint e t) ind = "(" ++ pshowExpr e ind ++ " : " ++ show t ++ ")"
pshowExpr (EVar x) _ = "x" ++ (subscript $ show $ uid x)
pshowExpr (EFun p e) ind = "fun " ++ show p ++ " ->\n" ++ ind ++ "    " ++ pshowExpr e (ind ++ "    ")
pshowExpr (ELet p e1 e2) ind = "let " ++ show p ++ " = " ++ pshowExpr e1 ind ++ " in\n" ++ ind ++ pshowExpr e2 ind
pshowExpr (EApp e1 e2) ind =
  (if is_atomic e1 then
     pshowExpr e1 ind
   else
     "(" ++ pshowExpr e1 ind ++ ")") ++ " " ++
  (if is_atomic e2 then
     pshowExpr e2 ind
   else
     "(" ++ pshowExpr e2 ind ++ ")")
pshowExpr (EBool b) _ = if b then "true" else "false"
pshowExpr (EPair e1 e2) ind = "<" ++ pshowExpr e1 ind ++ ", " ++ pshowExpr e2 ind ++ ">"
pshowExpr (EBox t) _ = "box[" ++ show t ++ "]"
pshowExpr (EUnbox e) ind =
  if is_atomic e then
    "unbox " ++ pshowExpr e ind
  else
    "unobx (" ++ pshowExpr e ind ++ ")"
pshowExpr (EIf e1 e2 e3) ind = "if " ++ pshowExpr e1 ind ++ " then\n" ++
                       ind ++ "  " ++ pshowExpr e2 (ind ++ "  ") ++ "\nelse\n" ++
                       ind ++ "  " ++ pshowExpr e3 (ind ++ "  ")
pshowExpr ERev _ = "rev"
pshowExpr (ELocated e _) ind = pshowExpr e ind

instance PShow Expr where
  pshow e = pshowExpr e "" 

