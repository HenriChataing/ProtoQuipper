-- | Provides all the printing functions of the surface syntax
module Printer where

import Classes

import Syntax

import Text.PrettyPrint.HughesPJ as PP
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

  sprintn lv (TTensor (a:rest)) =
    let dlv = decr lv in
    (case a of
       TArrow _ _ -> "(" ++ sprintn dlv a ++ ")"
       TTensor _ -> "(" ++ sprintn dlv a ++ ")"
       _ -> sprintn dlv a) ++
    List.foldl (\s b -> s ++ " * " ++
                  (case b of
                     TArrow _ _ -> "(" ++ sprintn dlv b ++ ")"
                     TTensor _ -> "(" ++ sprintn dlv b ++ ")"
                     _ -> sprintn dlv a)) "" rest

  sprintn lv (TArrow a b) =
    let dlv = decr lv in
    sprintn dlv a ++ " -> " ++
    (case b of
       TTensor _ -> "(" ++ sprintn dlv b ++ ")"
       TArrow _ _ -> "(" ++ sprintn dlv b ++ ")"
       _ -> sprintn dlv b)

  sprintn lv (TBang a) =
    "!" ++ (case a of
              TBang a -> sprintn lv a
              TTensor _ -> "(" ++ sprintn lv a ++ ")"
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

  sprintn lv (PTuple plist) =
    let dlv = decr lv in
    case plist of
      [] -> "<>"
      [p] -> "<" ++ sprintn dlv p ++ ">"
      p:rest -> "<" ++ sprintn dlv p ++ List.foldl (\s q -> s ++ ", " ++ sprintn dlv q) "" rest ++ ">"

  sprintn lv (PDatacon dcon Nothing) = dcon
  sprintn lv (PDatacon dcon (Just p)) = dcon ++ " (" ++ pprint p ++ ")"

  sprintn lv (PConstraint p t) = "(" ++ sprintn (decr lv) p ++ " : " ++ pprint t ++ ")"

  sprintn lv (PLocated p _) = sprintn lv p

  -- Print unto Lvl = +oo
  pprint p = sprintn Inf p
 
  -- Print unto Lvl = default
  sprint p = sprintn defaultLvl p



{- Expression printing -}

-- | Print the expression as a PP document
print_doc :: Expr -> Doc

print_doc EUnit = text "<>"
print_doc (EVar x) = text x
print_doc ERev = text "rev"
print_doc EUnbox = text "unbox"
print_doc (EBox a) = text "box" <> brackets (text $ pprint a)
print_doc (EBool b) = if b then text "true" else text "false"

print_doc (ELet p e f) =
  let pf = print_doc f in
  text "let" <+> text (pprint p) <+> equals <+> print_doc e <+> text "in" $$
  pf

print_doc (ETuple elist) =
  let plist = List.map print_doc elist in
  let slist = punctuate comma (List.init plist) ++ [List.last plist] in
  char '<' <> hsep plist <> char '>'

print_doc (EIf e f g) =
  text "if" <+> print_doc e <+> text "then" $$
  nest 2 (print_doc f) $$
  text "else" $$
  nest 2 (print_doc g)

print_doc (EApp e f) =
  let pe = print_doc e
      pf = print_doc f in
  (case e of
     EIf _ _ _ -> parens pe
     EFun _ _ -> parens pe
     _ -> pe) <+> 
  (case f of
     EIf _ _ _ -> parens pe 
     EFun _ _ -> parens pe
     EApp _ _ -> parens pe
     _ -> pe)

print_doc (EFun p e) =
  text "fun" <+> text (pprint p) <+> text "->" $$
  nest 4 (print_doc e)

print_doc (EDatacon datacon Nothing) =
  text datacon

print_doc (EDatacon datacon (Just e)) =
  let pe = print_doc e in
  text datacon <+> (case e of
                      EVar _ -> pe
                      EBool _ -> pe
                      EUnit -> pe
                      _ -> parens pe)

print_doc (EMatch e plist) =
  text "match" <+> print_doc e <+> text "with" $$
    nest 2 (List.foldl (\doc (p, f) ->
                          let pmatch = char '|' <+> text (pprint p) <+> text "->" <+> print_doc f in
                          if isEmpty doc then
                            pmatch
                          else
                            doc $$ pmatch) PP.empty plist)


print_doc (EConstraint e t) = print_doc e
print_doc (ELocated e _) = print_doc e
 
instance PPrint Expr where
  sprintn lv e = PP.render $ print_doc e
  sprint e = sprintn defaultLvl e
  pprint e = sprintn Inf e

