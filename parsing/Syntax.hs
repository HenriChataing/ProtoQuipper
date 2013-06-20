module Syntax where

import Data.Char
import Data.Map

import Localizing
import Classes

---------------------------------
-- Representation of Quipper's --
-- types                       --

data Type =
    TVar String               -- a
  | TUnit                     -- T
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

-- Eq instance declaration of types
-- The declaration takes into account the ismorphism : !! A = ! A
instance Eq Type where
  (==) (TLocated t1 _) t2 = t1 == t2
  (==) t1 (TLocated t2 _) = t1 == t2
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

  locate_opt t Nothing = t
  locate_opt t (Just ex) = locate t ex

  clear_location (TLocated t _) = clear_location t
  clear_location (TCirc t u) = TCirc (clear_location t) (clear_location u)
  clear_location (TTensor t u) = TTensor (clear_location t) (clear_location u)
  clear_location (TArrow t u) = TArrow (clear_location t) (clear_location u)
  clear_location (TExp t) = TExp (clear_location t)
  clear_location t = t
 
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

  locate_opt p Nothing = p
  locate_opt p (Just ex) = locate p ex

  clear_location (PLocated p _) = clear_location p
  clear_location (PPair p q) = PPair (clear_location p) (clear_location q)
  clear_location (PConstraint p t) = PConstraint (clear_location p) t
  clear_location p = p

instance Constraint Pattern where
  drop_constraints (PConstraint p _) = p
  drop_constraints (PPair p1 p2) = PPair (drop_constraints p1) (drop_constraints p2)
  drop_constraints (PLocated p ex) = PLocated (drop_constraints p) ex
  drop_constraints p = p

-- Translate an pattern into the matching expression
expr_of_pattern :: Pattern -> Expr
----------------------------------
expr_of_pattern PUnit = EUnit
expr_of_pattern (PVar x) = EVar x
expr_of_pattern (PPair p q) = EPair (expr_of_pattern p) (expr_of_pattern q)
expr_of_pattern (PLocated p ex) = ELocated (expr_of_pattern p) ex

pattern_of_expr :: Expr -> Pattern
----------------------------------
pattern_of_expr EUnit = PUnit
pattern_of_expr (EVar x) = PVar x
pattern_of_expr (EPair e f) = PPair (pattern_of_expr e) (pattern_of_expr f)
pattern_of_expr (ELocated e ex) = PLocated (pattern_of_expr e) ex

{-
   Instance declarations and functions of data type Expr :
  
   Expr is instance of :
     -- Show
     -- Constraint
     -- Located

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

  locate_opt e Nothing = e
  locate_opt e (Just ex) = locate e ex

  clear_location (ELocated e _) = clear_location e
  clear_location (EConstraint e t) = EConstraint (clear_location e) t
  clear_location (EFun p e) = EFun (clear_location p) (clear_location e)
  clear_location (ELet p e f) = ELet (clear_location p) (clear_location e) (clear_location f)
  clear_location (EApp e f) = EApp (clear_location e) (clear_location f)
  clear_location (EPair e f) = EPair (clear_location e) (clear_location f)
  clear_location (EIf e f g) = EIf (clear_location e) (clear_location f) (clear_location g)
  clear_location (EUnbox e) = EUnbox (clear_location e)
  clear_location (EBox t) = EBox (clear_location t)
  clear_location e = e

instance Constraint Expr where
  drop_constraints (EConstraint e _) = e
  drop_constraints (ELocated e ex) = ELocated (drop_constraints e) ex
  drop_constraints (EFun p e) = EFun (drop_constraints p) (drop_constraints e)
  drop_constraints (ELet p e1 e2) = ELet (drop_constraints p) (drop_constraints e1) (drop_constraints e2)
  drop_constraints (EApp e1 e2) = EApp (drop_constraints e1) (drop_constraints e2)
  drop_constraints (EPair e1 e2) = EPair (drop_constraints e1) (drop_constraints e2)
  drop_constraints (EIf e1 e2 e3) = EIf (drop_constraints e1) (drop_constraints e2) (drop_constraints e3)
  drop_constraints (EUnbox e) = EUnbox (drop_constraints e)
  drop_constraints e = e


