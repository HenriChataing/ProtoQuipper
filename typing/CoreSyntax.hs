module CoreSyntax where

import Classes
import Utils

import Data.List as List

-----------------------
-- Type renaming     --

type Variable = Int
type Flag = Int   -- 0 and 1 are reserved, -1 represents any value (for types like bool which can be either !bool or bool), and all others are flag variables

---------------------------------
-- Representation of Quipper's --
-- types                       --

-- Set of linear types (no ! annotation)
data LinType =
    TVar Variable              -- a
  | TBool                      -- bool
  | TUnit                      -- 1
  | TQBit                      -- qbit
  | TTensor Type Type          -- a * b
  | TArrow Type Type           -- a -> b
  | TCirc Type Type            -- circ (a, b)

data Type =
  -- Unit, circ and bool types are implicitely duplicable, so it is not necessary to give a bang annotation
--    TUnit                      -- !n T
--  | TBool                      -- !n bool
--  | TCirc Type Type            -- circ (a, b)
    TExp Flag LinType          -- !n a

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
  | EBool Bool                          -- True / False
  | EVar Variable                       -- x
  | EFun Pattern Expr                   -- fun p -> t
  | ELet Pattern Expr Expr              -- let p = e in f
  | EApp Expr Expr                      -- t u
  | EPair Expr Expr                     -- <t, u>
  | EIf Expr Expr Expr                  -- if e then f else g
  | EBox Type                           -- box[T]
  | EUnbox Expr                         -- unbox t

---------------------------------
-- Instance declarations       --

instance Param Pattern where
  free_var PUnit = []
  free_var (PVar x) = [x]
  free_var (PPair p q) = List.union (free_var p) (free_var q)

  subs_var _ _ p = p

instance Param Expr where
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

  free_var (EIf e f g) =
    List.union (List.union (free_var e) (free_var f)) (free_var g)

  free_var (EUnbox t) =
    free_var t
  
  free_var _ =
    []

  subs_var _ _ e = e

-------------------------------

instance Param LinType where
  free_var (TVar x) = [x]
  free_var (TTensor t u) = List.union (free_var t) (free_var u)
  free_var (TArrow t u) = List.union (free_var t) (free_var u)
  free_var (TCirc t u) = List.union (free_var t) (free_var u)
  free_var _ = []

  subs_var a b (TVar x) | x == a = TVar b
                        | otherwise = TVar x
  subs_var _ _ TUnit = TUnit
  subs_var _ _ TBool = TBool
  subs_var a b (TArrow t u) = TArrow (subs_var a b t) (subs_var a b u)
  subs_var a b (TTensor t u) = TTensor (subs_var a b t) (subs_var a b u)
  subs_var a b (TCirc t u) = TCirc (subs_var a b t) (subs_var a b u)

instance Param Type where
  free_var (TExp _ t) = free_var t
  subs_var a b (TExp n t) = TExp n (subs_var a b t)

-----------------------
-- Comparable things --

-- Eq instance declaration of types
-- The declaration takes into account the ismorphism : !! A = ! A
instance Eq LinType where
  (==) (TVar x) (TVar y) = x == y
  (==) TUnit TUnit = True
  (==) TBool TBool = True
  (==) TQBit TQBit = True
  (==) (TTensor t u) (TTensor t' u') = (t == t') && (u == u')
  (==) (TArrow t u) (TArrow t' u') = (t == t') && (u == u')
  (==) (TCirc t u) (TCirc t' u') = (t == t') && (u == u')
  (==) _ _ = False

instance Eq Type where
  (==) (TExp m t) (TExp n t') = m == n && t == t'

--------------
-- Printing --

{- Flag printing -}

instance PPrint Flag where
  sprintn _ n | n <= 0 = ""
              | n == 1 = "!"
              | otherwise = "!" ++ (superscript $ show n)

  sprint n = sprintn defaultLvl n
  pprint n = sprintn Inf n

{- Type printing -}

instance PPrint LinType where
  -- Print unto Lvl = n
  sprintn _ (TVar x) = subscript ("X" ++ show x)
  sprintn _ TUnit = "T"
  sprintn _ TBool = "bool"
  sprintn _ TQBit = "qbit"
  sprintn (Nth 0) _ = "..."

  sprintn lv (TTensor a b) =
    let dlv = decr lv in
    (case a of
       TExp _ (TArrow _ _) -> "(" ++ sprintn dlv a ++ ")"
       TExp _ (TTensor _ _) -> "(" ++ sprintn dlv a ++ ")"
       _ -> sprintn dlv a) ++ " * " ++
    (case b of
       TExp _ (TArrow _ _) -> "(" ++ sprintn dlv b ++ ")"
       TExp _ (TTensor _ _) -> "(" ++ sprintn dlv b ++ ")"
       _ -> sprintn dlv b)

  sprintn lv (TArrow a b) =
    let dlv = decr lv in
    (case a of
       TExp _ (TArrow _ _) -> "(" ++ sprintn dlv a ++ ")"
       _ -> sprintn dlv a) ++ " -> " ++
    sprintn dlv b

  sprintn lv (TCirc a b) =
    let dlv = decr lv in
    "circ(" ++ sprintn dlv a ++ ", " ++ sprintn dlv b ++ ")"

  -- Print unto Lvl = +oo
  pprint a = sprintn Inf a

  -- Print unto Lvl = default
  sprint a = sprintn defaultLvl a

instance PPrint Type where
  sprintn lv (TExp f a) =
    let pf = pprint f in
    if List.length pf == 0 then
      pf ++ sprintn lv a
    else
      pf ++ (case a of
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
indent_sprintn _ _ (EBool b) = if b then "true" else "false"
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

indent_sprintn lv ind (EIf e f g) =
  let dlv = decr lv in
  "if " ++ indent_sprintn dlv ind e ++ " then\n" ++
  ind ++ "  " ++ indent_sprintn dlv (ind ++ "  ") f ++ "\n" ++
  ind ++ "else\n" ++
  ind ++ "  " ++ indent_sprintn dlv (ind ++ "  ") g

indent_sprintn _ _ (EBox t) =
  "box[" ++ pprint t ++ "]"

indent_sprintn lv ind (EUnbox t) =
  "unbox (" ++ indent_sprintn (decr lv) ind t ++ ")"
 
instance PPrint Expr where
  sprintn lv e = indent_sprintn lv "" e
  sprint e = sprintn defaultLvl e
  pprint e = sprintn Inf e

