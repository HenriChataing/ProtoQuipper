module Syntax where

import Localizing
import Classes

import Data.Char
import Data.Map
import Data.List as List

-- | A data constructor is defined by its name
type Datacon = String


-- | Type declarations
-- For now, types takes no type argument
-- The definition is a list of pairs datacon * type
data Typedef = Typedef String [(Datacon, Type)]


-- | Definition of types
data Type =
    TVar String               -- a
  | TUnit                     -- T
  | TBool                     -- bool
  | TQBit                     -- qbit
  | TCirc Type Type           -- circ (A, B)
  | TTensor [Type]            -- A1 * .. * An
  | TArrow Type Type          -- A -> B
  | TExp Type                 -- !A
  | TApp Type Type            -- generic types specialization
  | TLocated Type Extent      -- A @ ex
  deriving Show


-- | Definition of patterns
-- Note : - the tuples are required to have a size >= 2. This much is enforced by the parsing grammar,
-- the program must be cautious not to change it
--        - should PUnit be written as PTuple [] ?
data Pattern =
    PUnit                     -- <>
  | PVar String               -- x
  | PTuple [Pattern]          -- <x1, .., xn>
  | PData Datacon Pattern     -- datacon (p)
  | PConstraint Pattern Type  -- (x : A)
  | PLocated Pattern Extent   -- x @ ex
  deriving Show


-- | Definition of terms
data Expr =
    EUnit                          -- <>
  | EVar String                    -- x  
  | EFun Pattern Expr              -- fun p -> e
  | ELet Pattern Expr Expr         -- let p = e in f
  | EApp Expr Expr                 -- e f
  | EBool Bool                     -- true / false
  | ETuple [Expr]                  -- <e1, .., en>
  | EData String Expr              -- datacon e
  | EMatch Expr [(Pattern, Expr)]  -- match e with (x1 -> f1) (x2 -> f2) ...(xn -> fn)
  | EBox Type                      -- box[A]
  | EUnbox                         -- unbox
  | EIf Expr Expr Expr             -- if e then f else g
  | ERev                           -- rev
  | EConstraint Expr Type          -- (e : A)
  | ELocated Expr Extent           -- e @ ex
  deriving Show


{-
   Instance declarations and functions of data type Type :   
  
   Type is instance of :
     -- Show
     -- PPrint / SPrint
     -- Located
     -- Eq

   Functions declared :
     -- extractVariables :: Type -> [String]
     -- subst :: String -> Type -> Type -> Type
     -- substAll :: Map String Type -> Type -> Type
     -- appSubst :: Map String Type -> Type -> Type
-}

-- Eq instance declaration of types
-- The declaration takes into account the ismorphism : !! A = ! A
instance Eq Type where
  (==) (TLocated t1 _) t2 = t1 == t2
  (==) t1 (TLocated t2 _) = t1 == t2
  (==) TUnit TUnit = True
  (==) TBool TBool = True
  (==) TQBit TQBit = True
  (==) (TCirc t1 t2) (TCirc t1' t2') = (t1 == t1') && (t2 == t2')
  (==) (TTensor tlist) (TTensor tlist') = (tlist == tlist')
  (==) (TArrow t1 t2) (TArrow t1' t2') = (t1 == t1') && (t2 == t2')
  (==) (TExp t1) (TExp t2) = (t1 == t2)
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
  clear_location (TTensor tlist) = TTensor $ List.map clear_location tlist
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
  clear_location (PTuple plist) = PTuple $ List.map clear_location plist
  clear_location (PConstraint p t) = PConstraint (clear_location p) t
  clear_location p = p

instance Constraint Pattern where
  drop_constraints (PConstraint p _) = p
  drop_constraints (PTuple plist) = PTuple $ List.map drop_constraints plist
  drop_constraints (PLocated p ex) = PLocated (drop_constraints p) ex
  drop_constraints p = p

-- Translate an pattern into the matching expression
expr_of_pattern :: Pattern -> Expr
----------------------------------
expr_of_pattern PUnit = EUnit
expr_of_pattern (PVar x) = EVar x
expr_of_pattern (PTuple plist) = ETuple $ List.map expr_of_pattern plist
expr_of_pattern (PLocated p ex) = ELocated (expr_of_pattern p) ex

pattern_of_expr :: Expr -> Pattern
----------------------------------
pattern_of_expr EUnit = PUnit
pattern_of_expr (EVar x) = PVar x
pattern_of_expr (ETuple elist) = PTuple $ List.map pattern_of_expr elist
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
isValue EUnbox = True
isValue ERev = True
isValue (ETuple elist) = List.and $ List.map isValue elist
isValue (EIf _ _ _) = False
isValue (EApp _ _) = False
isValue (ELet _ _ _) = False
isValue (EData _ e) = isValue e
isValue (EMatch _ _) = False
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
  clear_location (ETuple elist) = ETuple $ List.map clear_location elist
  clear_location (EIf e f g) = EIf (clear_location e) (clear_location f) (clear_location g)
  clear_location (EBox t) = EBox (clear_location t)
  clear_location (EData datacon e) = EData datacon (clear_location e)
  clear_location (EMatch e plist) = EMatch (clear_location e) $ List.map (\(p, f) -> (clear_location p, clear_location f)) plist
  clear_location e = e

instance Constraint Expr where
  drop_constraints (EConstraint e _) = e
  drop_constraints (ELocated e ex) = ELocated (drop_constraints e) ex
  drop_constraints (EFun p e) = EFun (drop_constraints p) (drop_constraints e)
  drop_constraints (ELet p e1 e2) = ELet (drop_constraints p) (drop_constraints e1) (drop_constraints e2)
  drop_constraints (EApp e1 e2) = EApp (drop_constraints e1) (drop_constraints e2)
  drop_constraints (ETuple elist) = ETuple $ List.map drop_constraints elist
  drop_constraints (EIf e1 e2 e3) = EIf (drop_constraints e1) (drop_constraints e2) (drop_constraints e3)
  drop_constraints (EData datacon e) = EData datacon (drop_constraints e)
  drop_constraints (EMatch e plist) = EMatch (drop_constraints e) $ List.map (\(p, f) -> (drop_constraints p, drop_constraints f)) plist
  drop_constraints e = e


