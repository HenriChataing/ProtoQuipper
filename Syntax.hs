module Syntax where

import Data.Char
import Data.Map

import Localizing

---------------------------------
-- Class of objects that can   --
-- be assorted with a location --

class Located a where
  locate :: a -> Extent -> a
  locateOpt :: a -> Maybe Extent -> a
  location :: a -> Maybe Extent

class Atomic a where
  isAtomic :: a -> Bool

class Constraint a where
  dropConstraints :: a -> a

---------------------------------
-- Representation of Quipper's --
-- types                       --

data Type =
    TVar String
  | TUnit
  | TUnknown
  | TBool
  | TQBit
  | TCirc Type Type
  | TTensor Type Type
  | TArrow Type Type
  | TExp Type
  | TLocated Type Extent

---------------------------------
-- Representation of patterns  --

data Pattern =
    PUnit
  | PVar String
  | PPair Pattern Pattern
  | PConstraint Pattern Type
  | PLocated Pattern Extent

---------------------------------
-- Quipper's terms             --

data Expr =
    EUnit
  | EConstraint Expr Type
  | EVar String
  | EFun Pattern Expr
  | ELet Pattern Expr Expr
  | EApp Expr Expr
  | EBool Bool
  | EPair Expr Expr
  | EBox Type
  | EUnbox Expr
  | ECirc Expr Expr Expr
  | EIf Expr Expr Expr
  | ERev
  | ELocated Expr Extent



{-
   Instance declarations and functions of data type Type :   
  
   Type is instance of :
     -- Show
     -- Atomic
     -- Located
     -- Eq

   Functions declared :
     -- stripExp :: Type -> Type
     -- stripExpRec :: Type -> Type
     -- reduceExp :: Type -> Type
     -- reduceExpRec :: Type -> Type
     -- extractVariables :: Type -> [String]
     -- subst :: String -> Type -> Type -> Type
     -- substAll :: Map String Type -> Type -> Type
     -- appSubst :: Map String Type -> Type -> Type
-}


-- Remove all ! annotations from type (not recursive)
stripExp :: Type -> Type
------------------------
stripExp (TExp t) = stripExp t
stripExp t = t

-- Recursively remove all ! annotations
stripExpRec :: Type -> Type
---------------------------
stripExpRec (TLocated a ex) = TLocated (stripExpRec a) ex
stripExpRec (TExp a) = stripExpRec a
stripExpRec (TTensor a b) = TTensor (stripExpRec a) (stripExpRec b)
stripExpRec (TCirc a b) = TCirc (stripExpRec a) (stripExpRec b)
stripExpRec (TArrow a b) = TArrow (stripExpRec a) (stripExpRec b)
stripExpRec a = a

-- Reduce all ! annotations to one
reduceExp :: Type -> Type
-------------------------
reduceExp (TExp (TExp a)) = reduceExp (TExp a)
reduceExp a = a

-- Recursively reduce all ! annotations
reduceExpRec :: Type -> Type
----------------------------
reduceExpRec (TLocated t ex) = TLocated (reduceExpRec t) ex
reduceExpRec (TExp (TExp a)) = reduceExpRec (TExp a)
reduceExpRec (TExp a) = TExp (reduceExpRec a)
reduceExpRec (TTensor a b) = TTensor (reduceExpRec a) (reduceExpRec b)
reduceExpRec (TCirc a b) = TCirc (reduceExpRec a) (reduceExpRec b)
reduceExpRec (TArrow a b) = TArrow (reduceExpRec a) (reduceExpRec b)

-- Eq instance declaration of types
-- The declaration takes into account the ismorphism : !! A = ! A
instance Eq Type where
  (==) (TLocated t1 _) t2 = t1 == t2
  (==) t1 (TLocated t2 _) = t1 == t2
  (==) (TVar v1) (TVar v2) = v1 == v2
  (==) TUnit TUnit = True
  (==) TBool TBool = True
  (==) TQBit TQBit = True
  (==) (TCirc t1 t2) (TCirc t1' t2') = (t1 == t1') && (t2 == t2')
  (==) (TTensor t1 t2) (TTensor t1' t2') = (t1 == t1') && (t2 == t2')
  (==) (TArrow t1 t2) (TArrow t1' t2') = (t1 == t1') && (t2 == t2')
  (==) (TExp t1) (TExp t2) = (stripExp t1 == stripExp t2)
  (==) _ _ = False

instance Atomic Type where
  isAtomic (TTensor _ _) = False
  isAtomic (TArrow _ _) = False
  isAtomic (TLocated t _) = isAtomic t
  isAtomic _ = True

instance Located Type where
  locate (TLocated t ex) _ = TLocated t ex
  locate t ex = TLocated t ex
  location (TLocated _ ex) = Just ex
  location _ = Nothing
  locateOpt t Nothing = t
  locateOpt t (Just ex) = locate t ex

instance Show Type where
  show (TVar s) = s
  show TUnit = "T"
  show TBool = "bool"
  show TQBit = "qbit"
  show TUnknown = "???"
  show (TCirc t1 t2) = "circ (" ++ show t1 ++ ", " ++ show t2 ++ ")"
  show (TTensor t1 t2) =
    (if isAtomic t1 then show t1
     else "(" ++ show t1 ++ ")") ++ " * " ++
    (if isAtomic t2 then show t2
     else "(" ++ show t2 ++ ")")
  show (TLocated t _) = show t
  show (TExp t) = "!" ++ (if isAtomic t then show t else "(" ++ show t ++ ")")
  show (TArrow t1 t2) =
    (if isAtomic t1 then show t1
     else "(" ++ show t1 ++ ")") ++ " -> " ++
    (if isAtomic t2 then show t2
     else "(" ++ show t2 ++ ")")

-- Extract all the free type variables
extractVariables :: Type -> [String]
------------------------------------
extractVariables (TLocated t _) = extractVariables t
extractVariables (TVar x) = [x]
extractVariables (TTensor t1 t2) = extractVariables t1 ++ extractVariables t2
extractVariables (TCirc t1 t2) = extractVariables t1 ++ extractVariables t2
extractVariables (TArrow t1 t2) = extractVariables t1 ++ extractVariables t2
extractVariables (TExp t) = extractVariables t
extractVariables _ = []

-- Substitute type variable x by type a in type t
subst :: String -> Type -> Type -> Type
---------------------------------------
subst x a (TLocated t ex) = TLocated (subst x a t) ex
subst x a (TVar y) | x == y = a
                   | otherwise = TVar y
subst x a (TTensor t1 t2) = TTensor (subst x a t1) (subst x a t2)
subst x a (TCirc t1 t2) = TCirc (subst x a t1) (subst x a t2)
subst x a (TArrow t1 t2) = TArrow (subst x a t1) (subst x a t2)
subst x a (TExp t) = TExp (subst x a t)
subst _ _ t = t

-- Apply all the substitutions defined by the map
substAll :: Map String Type -> Type -> Type
-------------------------------------------
substAll sub (TLocated t ex) = TLocated (substAll sub t) ex
substAll sub (TVar x) =
  case Data.Map.lookup x sub of
  Just t -> t
  Nothing -> TVar x
substAll sub (TTensor t1 t2) = TTensor (substAll sub t1) (substAll sub t2)
substAll sub (TCirc t1 t2) = TCirc (substAll sub t1) (substAll sub t2)
substAll sub (TArrow t1 t2) = TArrow (substAll sub t1) (substAll sub t2)
substAll sub (TExp t) = TExp (substAll sub t)
substAll _ t = t

-- Apply the substitution until the fixpoint is attained
appSubst :: Map String Type -> Type -> Type
-------------------------------------------
appSubst sub t =
  let t' = substAll sub t in
  if t == t' then
    t
  else
    appSubst sub t'


{-
   Instance declarations and functions of data type Pattern :   
  
   Pattern is instance of :
     -- Show
     -- Constraint
     -- Located

   Functions declared :
     --
-}

instance Located Pattern where
  locate (PLocated p ex) _ = PLocated p ex
  locate p ex = PLocated p ex
  location (PLocated _ ex) = Just ex
  location _ = Nothing
  locateOpt p Nothing = p
  locateOpt p (Just ex) = locate p ex

instance Show Pattern where
  show (PLocated p _) = show p
  show (PVar s) = s
  show (PPair p1 p2) = "<" ++ show p1 ++ ", " ++ show p2 ++ ">"
  show PUnit = "<>"

instance Constraint Pattern where
  dropConstraints (PConstraint p _) = p
  dropConstraints (PPair p1 p2) = PPair (dropConstraints p1) (dropConstraints p2)
  dropConstraints (PLocated p ex) = PLocated (dropConstraints p) ex
  dropConstraints p = p

{-
   Instance declarations and functions of data type Expr :
  
   Expr is instance of :
     -- Show
     -- Constraint
     -- Located
     -- Atomic

   Functions declared :
     -- isValue :: Expr -> Bool 
-}


-- Value identification
isValue :: Expr -> Bool
-----------------------
isValue (ELocated e _) = isValue e
isValue (EConstraint e _) = isValue e
isValue (EUnbox (ECirc _ _ _)) = True
isValue (EUnbox _) = False
isValue (EPair e1 e2) = isValue e1 && isValue e2
isValue (EIf _ _ _) = False
isValue (EApp _ _) = False
isValue (ELet _ _ _) = False
isValue _ = True

instance Located Expr where
  locate (ELocated e ex) _ = ELocated e ex
  locate e ex = ELocated e ex
  location (ELocated _ ex) = Just ex
  location _ = Nothing
  locateOpt e Nothing = e
  locateOpt e (Just ex) = locate e ex

instance Atomic Expr where
  isAtomic (ELocated e _) = isAtomic e
  isAtomic (EApp _ _) = False
  isAtomic (EIf _ _ _) = False
  isAtomic (EFun _ _) = False
  isAtomic _ = True

instance Show Expr where
  show (ELocated e _) = show e
  show EUnit = "<>"
  show (EVar s) = s
  show (ELet p e1 e2) = "let " ++ show p ++ " = " ++ show e1 ++ " in\n " ++ show e2
  show (EBool b) = if b then "true" else "false"
  show (EPair e1 e2) = "<" ++ show e1 ++ ", " ++ show e2 ++ ">"
  show (EIf e1 e2 e3) = "if " ++ show e1 ++ " then\n " ++ show e2 ++ "\n else\n " ++ show e3
  show (EApp e1 e2) =
    (if isAtomic e1 then show e1
     else "(" ++ show e1 ++ ")") ++ " " ++
    (if isAtomic e2 then show e2
     else "(" ++ show e2 ++ ")")
  show (EUnbox e) = if isAtomic e then "unbox " ++ show e else "unbox (" ++ show e ++ ")"
  show ERev = "rev"
  show (EBox t) = "box[" ++ show t ++ "]"
  show (EFun p e) = "fun " ++ (show p) ++ " -> " ++ (show e)
  
instance Constraint Expr where
  dropConstraints (EConstraint e _) = e
  dropConstraints (ELocated e ex) = ELocated (dropConstraints e) ex
  dropConstraints (EFun p e) = EFun (dropConstraints p) (dropConstraints e)
  dropConstraints (ELet p e1 e2) = ELet (dropConstraints p) (dropConstraints e1) (dropConstraints e2)
  dropConstraints (EApp e1 e2) = EApp (dropConstraints e1) (dropConstraints e2)
  dropConstraints (EPair e1 e2) = EPair (dropConstraints e1) (dropConstraints e2)
  dropConstraints (EIf e1 e2 e3) = EIf (dropConstraints e1) (dropConstraints e2) (dropConstraints e3)
  dropConstraints (ECirc e1 e2 e3) = ECirc (dropConstraints e1) (dropConstraints e2) (dropConstraints e3)
  dropConstraints (EUnbox e) = EUnbox (dropConstraints e)
  dropConstraints e = e


