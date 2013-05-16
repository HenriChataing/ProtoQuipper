{- Contain all the printer instance declarations of the surface syntax -}
module Printer where

import Classes

import Syntax

{- Type printing -}

instance PPrint Type where
  -- Print unto Lvl = n
  sprintn _ (TVar x) = x
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
indentSprintn :: Lvl -> String -> Expr -> String
------------------------------------------------
indentSprintn _ _ EUnit = "<>"
indentSprintn _ _ (EVar x) = x
indentSprintn _ _ ERev = "rev"
indentSprintn _ _ (EBox a) = "box[" ++ pprint a ++ "]"
indentSprintn _ _ (EBool b) = if b then "true" else "false"

indentSprintn (Nth 0) _ _ = "..."

indentSprintn lv ind (ELet p e f) =
  let dlv = decr lv in
  "let " ++ sprintn dlv p ++ " = " ++ indentSprintn dlv ind e ++ " in\n" ++
  ind ++ indentSprintn dlv ind f

indentSprintn lv ind (EPair e f) =
  "<" ++ indentSprintn (decr lv) ind e ++ ", " ++ indentSprintn (decr lv) ind f ++ ">"

indentSprintn lv ind (EIf e f g) =
  let dlv = decr lv in
  "if " ++ indentSprintn dlv ind e ++ " then\n" ++
  ind ++ "  " ++ indentSprintn dlv (ind ++ "  ") f ++ "\n else\n" ++
  ind ++ "  " ++ indentSprintn dlv (ind ++ "  ") g

indentSprintn lv ind (EApp e f) =
  let dlv = decr lv in
  (case e of
     EIf _ _ _ -> "(" ++ indentSprintn dlv ind e ++ ")"
     EFun _ _ -> "(" ++ indentSprintn dlv ind e ++ ")"
     _ -> indentSprintn dlv ind e) ++ " " ++
  (case f of
     EIf _ _ _ ->  "(" ++ indentSprintn dlv ind f ++ ")"
     EFun _ _ -> "(" ++ indentSprintn dlv ind f ++ ")"
     EApp _ _ -> "(" ++ indentSprintn dlv ind f ++ ")"
     EUnbox _ -> "(" ++ indentSprintn dlv ind f ++ ")"
     _ -> indentSprintn dlv ind f)

indentSprintn lv ind (EUnbox e) =
  let dlv = decr lv in
  "unbox" ++ (case e of
                EIf _ _ _ -> "(" ++ indentSprintn dlv ind e ++ ")"
                EApp _ _ -> "(" ++ indentSprintn dlv ind e ++ ")"
                EFun _ _ -> "(" ++ indentSprintn dlv ind e ++ ")"
                EUnbox _ -> "(" ++ indentSprintn dlv ind e ++ ")"
                _ -> indentSprintn dlv ind e)

indentSprintn lv ind (EFun p e) =
  let dlv = decr lv in
  "fun " ++ sprintn dlv p ++ " ->\n" ++
  ind ++ "    " ++ indentSprintn dlv (ind ++ "    ") e

indentSprintn lv ind (EConstraint e t) = "(" ++ indentSprintn (decr lv) ind e ++ " : " ++ pprint t ++ ")"
indentSprintn lv ind (ELocated e _) = indentSprintn lv ind e
 
instance PPrint Expr where
  sprintn lv e = indentSprintn lv "" e
  sprint e = sprintn defaultLvl e
  pprint e = sprintn Inf e

