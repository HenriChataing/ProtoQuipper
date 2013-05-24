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
-- Quipper's terms             --

data Expr =
    EUnit                               -- *
  | EVar Variable                       -- x
  | EFun Variable Expr                  -- fun x -> t
  | ELet Variable Variable Expr Expr    -- let <x, y> = e in f
  | EApp Expr Expr                      -- t u
  | EPair Expr Expr                     -- <t, u>
  deriving Show

-- Extract all the variables
free_variables :: Expr -> [Int]
-------------------------------
free_variables EUnit = []
free_variables (EVar x) = [x]

free_variables (EFun x e) =
  let fve = free_variables e in
  List.delete x fve

free_variables (ELet x y e f) =
  let fve = free_variables e
      fvf = free_variables f in
  (fve ++ fvf) \\ [x, y]

free_variables (EApp e f) =
  free_variables e ++ free_variables f

free_variables (EPair e f) =
  free_variables e ++ free_variables f


-- Extract all the free type variables
free_type_variables :: Type -> [Int]
------------------------------------
free_type_variables (TVar x) = [x]
free_type_variables (TTensor t u) = free_type_variables t ++ free_type_variables u
free_type_variables (TArrow t u) = free_type_variables t ++ free_type_variables u
free_type_variables (TExp _ t) = free_type_variables t
free_type_variables _ = []

type Mapping = (Variable, Type)

-- Substitute type variable x by type a in type t
-- The flags are left untouched in the original type
subst :: Type -> Mapping -> Type
---------------------------------------
subst (TVar x) (y, a) | x == y = a
                      | otherwise = TVar x
subst (TTensor t u) m = TTensor (subst t m) (subst u m)
subst (TArrow t u) m = TArrow (subst t m) (subst u m)
subst (TExp f t) m = TExp f (subst t m)
subst t _ = t

type Substitution = [Mapping]

-- Apply all the substitutions defined by the map
subst_all :: Type -> Substitution -> Type
-------------------------------------------
subst_all (TVar x) sub =
  case List.lookup x sub of
  Just t -> t
  Nothing -> TVar x
subst_all (TTensor t u) sub = TTensor (subst_all t sub) (subst_all u sub)
subst_all (TArrow t u) sub = TArrow (subst_all t sub) (subst_all u sub)
subst_all (TExp f t) sub = TExp f (subst_all t sub)
subst_all t _ = t

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
       TArrow _ _ -> "(" ++ sprintn dlv a ++ ")"
       TTensor _ _ -> "(" ++ sprintn dlv a ++ ")"
       _ -> sprintn dlv a)

  sprintn lv (TArrow a b) =
    let dlv = decr lv in
    sprintn dlv a ++ " -> " ++
    (case b of
       TTensor _ _ -> "(" ++ sprintn dlv b ++ ")"
       TArrow _ _ -> "(" ++ sprintn dlv b ++ ")"
       _ -> sprintn dlv b)

  sprintn lv (TExp f a) =
    superscript ("!" ++ show f) ++
           (case a of
              TTensor _ _ -> "(" ++ sprintn lv a ++ ")"
              TArrow _ _ -> "(" ++ sprintn lv a ++ ")"
              _ -> sprintn lv a)

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

indent_sprintn lv ind (ELet x y e f) =
  let dlv = decr lv in
  "let <" ++ print_var x ++ ", " ++ print_var y ++ "> = " ++ indent_sprintn dlv ind e ++ " in\n" ++
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

indent_sprintn lv ind (EFun x e) =
  let dlv = decr lv in
  "fun " ++ print_var x ++ " ->\n" ++
  ind ++ "    " ++ indent_sprintn dlv (ind ++ "    ") e
 
instance PPrint Expr where
  sprintn lv e = indent_sprintn lv "" e
  sprint e = sprintn defaultLvl e
  pprint e = sprintn Inf e

