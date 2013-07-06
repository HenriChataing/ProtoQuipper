{- Contain all the printer instance declarations of the surface syntax -}
module Printer where

import Classes

import Syntax

import Data.List as List

{- Type printing -}

instance PPrint Type where
  -- Print unto Lvl = n
  sprintn _ TUnit = "T"
  sprintn _ TBool = "bool"
  sprintn _ TQBit = "qbit"
  sprintn (Nth 0) _ = "..."
  sprintn lv (TCirc a b) =
    "circ (" ++ sprintn (decr lv) a ++ ", " ++ sprintn (decr lv) b ++ ")"

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

  sprintn lv (TExp a) =
    "!" ++ (case a of
              TExp a -> sprintn lv a
              TTensor _ _ -> "(" ++ sprintn lv a ++ ")"
              TArrow _ _ -> "(" ++ sprintn lv a ++ ")"
              _ -> sprintn lv a)

  sprintn lv (TSum a b) =
    let dlv = decr lv in
    (case a of
       TSum _ _ -> "(" ++ sprintn dlv a ++ ")"
       _ -> sprintn dlv a) ++ " + " ++
    sprintn dlv b

  sprintn lv (TLocated a _) = sprintn lv a

  -- Print unto Lvl = +oo
  pprint a = sprintn Inf a

  -- Print unto Lvl = default
  sprint a = sprintn defaultLvl a



{- Pattern printing -}

instance PPrint Pattern where
  -- Print unto Lvl = n
  sprintn _ PUnit = "<>"
  sprintn _ (PVar x) = x
  sprintn (Nth 0) _ = "..."

  sprintn lv (PPair p q) = "<" ++ sprintn (decr lv) p ++ ", " ++ sprintn (decr lv) q ++ ">"
  sprintn lv (PConstraint p t) = "(" ++ sprintn (decr lv) p ++ " : " ++ pprint t ++ ")"
  sprintn lv (PLocated p _) = sprintn lv p

  -- Print unto Lvl = +oo
  pprint p = sprintn Inf p
 
  -- Print unto Lvl = default
  sprint p = sprintn defaultLvl p



{- Expression printing -}

-- Second argument is indentation level
indent_sprintn :: Lvl -> String -> Expr -> String
------------------------------------------------
indent_sprintn _ _ EUnit = "<>"
indent_sprintn _ _ (EVar x) = x
indent_sprintn _ _ ERev = "rev"
indent_sprintn _ _ (EBox a) = "box[" ++ pprint a ++ "]"
indent_sprintn _ _ (EBool b) = if b then "true" else "false"

indent_sprintn (Nth 0) _ _ = "..."

indent_sprintn lv ind (ELet p e f) =
  let dlv = decr lv in
  "let " ++ sprintn dlv p ++ " = " ++ indent_sprintn dlv ind e ++ " in\n" ++
  ind ++ indent_sprintn dlv ind f

indent_sprintn lv ind (EPair e f) =
  "<" ++ indent_sprintn (decr lv) ind e ++ ", " ++ indent_sprintn (decr lv) ind f ++ ">"

indent_sprintn lv ind (EIf e f g) =
  let dlv = decr lv in
  "if " ++ indent_sprintn dlv ind e ++ " then\n" ++
  ind ++ "  " ++ indent_sprintn dlv (ind ++ "  ") f ++ "\n" ++
  ind ++ "else\n" ++
  ind ++ "  " ++ indent_sprintn dlv (ind ++ "  ") g

indent_sprintn lv ind (EApp e f) =
  let dlv = decr lv in
  (case e of
     EIf _ _ _ -> "(" ++ indent_sprintn dlv ind e ++ ")"
     EFun _ _ -> "(" ++ indent_sprintn dlv ind e ++ ")"
     _ -> indent_sprintn dlv ind e) ++ " " ++
  (case f of
     EIf _ _ _ ->  "(" ++ indent_sprintn dlv ind f ++ ")"
     EFun _ _ -> "(" ++ indent_sprintn dlv ind f ++ ")"
     EApp _ _ -> "(" ++ indent_sprintn dlv ind f ++ ")"
     EUnbox _ -> "(" ++ indent_sprintn dlv ind f ++ ")"
     _ -> indent_sprintn dlv ind f)

indent_sprintn lv ind (EUnbox e) =
  let dlv = decr lv in
  "unbox" ++ (case e of
                EIf _ _ _ -> "(" ++ indent_sprintn dlv ind e ++ ")"
                EApp _ _ -> "(" ++ indent_sprintn dlv ind e ++ ")"
                EFun _ _ -> "(" ++ indent_sprintn dlv ind e ++ ")"
                EUnbox _ -> "(" ++ indent_sprintn dlv ind e ++ ")"
                _ -> indent_sprintn dlv ind e)

indent_sprintn lv ind (EFun p e) =
  let dlv = decr lv in
  "fun " ++ sprintn dlv p ++ " ->\n" ++
  ind ++ "    " ++ indent_sprintn dlv (ind ++ "    ") e

indent_sprintn lv ind (EInjL e) =
  "injl(" ++ indent_sprintn (decr lv) ind e ++ ")"

indent_sprintn lv ind (EInjR e) =
  "injr(" ++ indent_sprintn (decr lv) ind e ++ ")"

indent_sprintn lv ind (EMatch e plist) =
  let dlv = decr lv in
  "match " ++ indent_sprintn dlv ind e ++ " with" ++
    List.foldl (\s (p, f) -> s ++ "\n" ++ ind ++ "  | " ++ sprintn dlv p ++ " -> " ++ indent_sprintn dlv (ind ++ "    ") f) "" plist

indent_sprintn lv ind (EConstraint e t) = "(" ++ indent_sprintn (decr lv) ind e ++ " : " ++ pprint t ++ ")"
indent_sprintn lv ind (ELocated e _) = indent_sprintn lv ind e
 
instance PPrint Expr where
  sprintn lv e = indent_sprintn lv "" e
  sprint e = sprintn defaultLvl e
  pprint e = sprintn Inf e

