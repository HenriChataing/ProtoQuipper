module Syntax where

import Data.Char
import Data.Map

import Localizing
import Classes

---------------------------------
-- Representation of Quipper's --
-- types                       --

data Type =
    TUnit                     -- T
  | TVar String               -- a
  | TBool                     -- bool
  | TQBit                     -- qbit
  | TCirc Type Type           -- circ (A, B)
  | TTensor Type Type         -- A * B
  | TArrow Type Type          -- A -> B
  | TExp Type                 -- !A
  | TLocated Type Extent      -- A @ ex
  deriving Show

---------------------------------
-- Representation of patterns  --

data Pattern =
    PUnit                     -- *
  | PVar String               -- x
  | PPair Pattern Pattern     -- <x, y>
  | PConstraint Pattern Type  -- (x : A)
  | PLocated Pattern Extent   -- x @ ex
  deriving Show

---------------------------------
-- Quipper's terms             --

data Expr =
    EUnit                     -- *
  | EConstraint Expr Type     -- (e : A)
  | EVar String               -- x  
  | EFun Pattern Expr         -- fun p -> e
  | ELet Pattern Expr Expr    -- let p = e in f
  | EApp Expr Expr            -- e f
  | EBool Bool                -- true / false
  | EPair Expr Expr           -- <e, f>
  | EBox Type                 -- box[A]
  | EUnbox Expr               -- unbox e
  | EIf Expr Expr Expr        -- if e then f else g
  | ERev                      -- rev
  | ELocated Expr Extent      -- e @ ex
  deriving Show


{-
   Instance declarations and functions of data type Type :   
  
   Type is instance of :
     -- Show
     -- PPrint / SPrint
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
stripExp (TLocated t ex) = TLocated (stripExp t) ex
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
reduceExpRec a = a

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

instance Located Type where
  locate (TLocated t ex) _ = TLocated t ex
  locate t ex = TLocated t ex
  location (TLocated _ ex) = Just ex
  location _ = Nothing
  locateOpt t Nothing = t
  locateOpt t (Just ex) = locate t ex

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

instance Constraint Expr where
  dropConstraints (EConstraint e _) = e
  dropConstraints (ELocated e ex) = ELocated (dropConstraints e) ex
  dropConstraints (EFun p e) = EFun (dropConstraints p) (dropConstraints e)
  dropConstraints (ELet p e1 e2) = ELet (dropConstraints p) (dropConstraints e1) (dropConstraints e2)
  dropConstraints (EApp e1 e2) = EApp (dropConstraints e1) (dropConstraints e2)
  dropConstraints (EPair e1 e2) = EPair (dropConstraints e1) (dropConstraints e2)
  dropConstraints (EIf e1 e2 e3) = EIf (dropConstraints e1) (dropConstraints e2) (dropConstraints e3)
  dropConstraints (EUnbox e) = EUnbox (dropConstraints e)
  dropConstraints e = e


