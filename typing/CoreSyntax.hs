module CoreSyntax where

import Classes
import Utils

import Data.List as List

-----------------------
-- Type renaming     --

type Variable = Int
type Flag = Int

---------------------------------
-- Representation of Quipper's --
-- types                       --

data Type =
    TVar Variable              -- a
  | TUnit                      -- 1
  | TExp Flag Type             -- !n a 
  | TTensor Type Type          -- a * b
  | TArrow Type Type           -- a -> b

---------------------------------
-- Quipper's patterns          --

data Pattern =
    PUnit                      -- <>
  | PVar Variable              -- x
  | PPair Pattern Pattern      -- <p, q>
  deriving Show 

---------------------------------
-- Quipper's terms             --

data Expr =
    EUnit                               -- *
  | EVar Variable                       -- x
  | EFun Pattern Expr                   -- fun p -> t
  | ELet Pattern Expr Expr              -- let p = e in f
  | EApp Expr Expr                      -- t u
  | EPair Expr Expr                     -- <t, u>
  deriving Show

---------------------------------
-- Instance delcarations       --

instance Param Pattern where
  free_var PUnit = []
  free_var (PVar x) = [x]
  free_var (PPair p q) = List.union (free_var p) (free_var q)

  subs_var _ _ p = p
  subs _ _ p = p

instance Param Expr where
  free_var EUnit = []
  free_var (EVar x) = [x]
  
  free_var (EFun p e) = 
    let fve = free_var e
        fvp = free_var p in
    fve \\ fvp

  free_var (ELet p e f) =
    let fve = free_var e
        fvf = free_var f
        fvp = free_var p in
    (List.union fve fvf) \\ fvp

  free_var (EApp e f) =
    List.union (free_var e) (free_var f)

  free_var (EPair e f) =
    List.union (free_var e) (free_var f)

  subs_var _ _ e = e
  subs _ _ e = e

-------------------------------

instance Param Type where
  free_var (TVar x) = [x]
  free_var (TTensor t u) = List.union (free_var t) (free_var u)
  free_var (TArrow t u) = List.union (free_var t) (free_var u)
  free_var (TExp _ t) = free_var t
  free_var _ = []

  subs_var a b (TVar x) | x == a = TVar b
                        | otherwise = TVar x
  subs_var _ _ TUnit = TUnit
  subs_var a b (TExp n t) = TExp n (subs_var a b t)
  subs_var a b (TArrow t u) = TArrow (subs_var a b t) (subs_var a b u)
  subs_var a b (TTensor t u) = TTensor (subs_var a b t) (subs_var a b u)

  subs x a (TVar y) | x == y = a
                    | otherwise = TVar y
  subs x a (TTensor t u) = TTensor (subs x a t) (subs x a u)
  subs x a (TArrow t u) = TArrow (subs x a t) (subs x a u)
  subs x a (TExp f t) = TExp f (subs x a t)
  subs _ _ t = t

-----------------------
-- Comparable things --

-- Eq instance declaration of types
-- The declaration takes into account the ismorphism : !! A = ! A
instance Eq Type where
  (==) (TVar x) (TVar y) = x == y
  (==) TUnit TUnit = True
  (==) (TTensor t u) (TTensor t' u') = (t == t') && (u == u')
  (==) (TArrow t u) (TArrow t' u') = (t == t') && (u == u')
  (==) (TExp _ t) (TExp _ t') = t == t'
  (==) _ _ = False

--------------
-- Printing --

{- Type printing -}

instance PPrint Type where
  -- Print unto Lvl = n
  sprintn _ (TVar x) = subscript ("X" ++ show x)
  sprintn _ TUnit = "T"
  sprintn (Nth 0) _ = "..."

  sprintn lv (TTensor a b) =
    let dlv = decr lv in
    (case a of
       TArrow _ _ -> "(" ++ sprintn dlv a ++ ")"
       _ -> sprintn dlv a) ++ " * " ++
    (case b of
       TArrow _ _ -> "(" ++ sprintn dlv b ++ ")"
       TTensor _ _ -> "(" ++ sprintn dlv b ++ ")"
       _ -> sprintn dlv b)

  sprintn lv (TArrow a b) =
    let dlv = decr lv in
    (case a of
       TArrow _ _ -> "(" ++ sprintn dlv a ++ ")"
       _ -> sprintn dlv a)  ++ " -> " ++
    sprintn dlv b

  sprintn lv (TExp f a) =
    (if f == 0 then
       ""
     else if f == 1 then
       "!"
     else
       superscript ("!" ++ show f)) ++
    (case a of
       TTensor _ _ -> "(" ++ sprintn lv a ++ ")"
       TArrow _ _ -> "(" ++ sprintn lv a ++ ")"
       _ -> sprintn lv a)

  -- Print unto Lvl = +oo
  pprint a = sprintn Inf a

  -- Print unto Lvl = default
  sprint a = sprintn defaultLvl a

{- Pattern printing -}

instance PPrint Pattern where
   -- Print unto Lvl = n
  sprintn _ (PVar x) = subscript ("x" ++ show x)
  sprintn _ PUnit = "<>"
  sprintn (Nth 0) _ = "..."

  sprintn lv (PPair a b) =
    let dlv = decr lv in
    "<" ++ sprintn dlv a ++ ", " ++ sprintn dlv b ++ ">"

  -- Print unto Lvl = +oo
  pprint a = sprintn Inf a

  -- Print unto Lvl = default
  sprint a = sprintn defaultLvl a


{- Expression printing -}

print_var x = subscript ("x" ++ show x)

-- Second argument is indentation level
indent_sprintn :: Lvl -> String -> Expr -> String
------------------------------------------------
indent_sprintn _ _ EUnit = "<>"
indent_sprintn _ _ (EVar x) = print_var x

indent_sprintn (Nth 0) _ _ = "..."

indent_sprintn lv ind (ELet p e f) =
  let dlv = decr lv in
  "let " ++ pprint p ++ " = " ++ indent_sprintn dlv ind e ++ " in\n" ++
  ind ++ indent_sprintn dlv ind f

indent_sprintn lv ind (EPair e f) =
  "<" ++ indent_sprintn (decr lv) ind e ++ ", " ++ indent_sprintn (decr lv) ind f ++ ">"

indent_sprintn lv ind (EApp e f) =
  let dlv = decr lv in
  (case e of
     EFun _ _ -> "(" ++ indent_sprintn dlv ind e ++ ")"
     _ -> indent_sprintn dlv ind e) ++ " " ++
  (case f of
     EFun _ _ -> "(" ++ indent_sprintn dlv ind f ++ ")"
     EApp _ _ -> "(" ++ indent_sprintn dlv ind f ++ ")"
     _ -> indent_sprintn dlv ind f)

indent_sprintn lv ind (EFun p e) =
  let dlv = decr lv in
  "fun " ++ pprint p ++ " ->\n" ++
  ind ++ "    " ++ indent_sprintn dlv (ind ++ "    ") e
 
instance PPrint Expr where
  sprintn lv e = indent_sprintn lv "" e
  sprint e = sprintn defaultLvl e
  pprint e = sprintn Inf e

