-- | This module provides the pretty printing functions necessary to render
-- the types and expressions of the core syntax

module CorePrinter where

import Classes
import Utils

import Syntax (RecFlag (..))
import CoreSyntax hiding ((<>))

import Text.PrettyPrint.HughesPJ as PP
import Data.List as List


instance PPrint LinType where
  -- Print unto Lvl = n
  sprintn _ (TVar x) = subvar 'X' x
  sprintn _ TUnit = "T"
  sprintn _ TBool = "bool"
  sprintn _ TQbit = "qbit"
  sprintn _ (TUser n app) = n ++ List.foldr (\t rec -> " " ++ pprint t ++ rec) "" app
  sprintn (Nth 0) _ = "..."

  sprintn lv (TTensor (a:rest)) =
    let dlv = decr lv in
    (case a of
       TBang _ (TArrow _ _) -> "(" ++ sprintn dlv a ++ ")"
       TBang _ (TTensor _) -> "(" ++ sprintn dlv a ++ ")"
       _ -> sprintn dlv a) ++
    List.foldl (\s b -> s ++ " * " ++
                  (case b of
                     TBang _ (TArrow _ _) -> "(" ++ sprintn dlv b ++ ")"
                     TBang _ (TTensor _) -> "(" ++ sprintn dlv b ++ ")"
                     _ -> sprintn dlv b)) "" rest

  sprintn lv (TArrow a b) =
    let dlv = decr lv in
    (case a of
       TBang _ (TArrow _ _) -> "(" ++ sprintn dlv a ++ ")"
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
  sprintn lv (TBang f a) =
    let pf = pprint f in
    if List.length pf == 0 then
      pf ++ sprintn lv a
    else
      pf ++ (case a of
               (TTensor _) -> "(" ++ sprintn lv a ++ ")"
               (TArrow _ _) -> "(" ++ sprintn lv a ++ ")"
               _ -> sprintn lv a)

  sprintn lv (TForall _ _ _ t) = 
    sprintn lv t
 
  -- Print unto Lvl = +oo
  pprint a = sprintn Inf a

  -- Print unto Lvl = default
  sprint a = sprintn defaultLvl a



instance PPrint Pattern where
   -- Print unto Lvl = n
  sprintn _ (PVar x) = subvar 'x' x
  sprintn _ PUnit = "<>"
  sprintn (Nth 0) _ = "..."

  sprintn lv (PTuple (p:rest)) =
    let dlv = decr lv in
    "<" ++ sprintn dlv p ++ List.foldl (\s q -> s ++ ", " ++ sprintn dlv q) "" rest ++ ">"

  sprintn lv (PDatacon dcon p) =
    subvar 'D' dcon ++ case p of
                         Just p -> "(" ++ sprintn (decr lv) p ++ ")"
                         Nothing -> ""

  sprintn lv (PLocated p _) =
    sprintn lv p

  -- Print unto Lvl = +oo
  pprint a = sprintn Inf a

  -- Print unto Lvl = default
  sprint a = sprintn defaultLvl a


-- | Print an expression as a pp document
print_doc :: Expr -> Doc
print_doc EUnit = text "<>"
print_doc (EBool b) = if b then text "true" else text "false"
print_doc (EVar x) = text $ subvar 'x' x
print_doc (EGlobal x) = text $ subvar 'x' x

print_doc (ELet r p e f) =
  let recflag = if r == Recursive then text "rec" else empty in
  text "let" <+> recflag <+> text (pprint p) <+> equals <+> print_doc e <+> text "in" $$
  print_doc f

print_doc (ETuple elist) =
  let plist = List.map print_doc elist in
  let slist = (punctuate comma $ List.init plist) ++ [List.last plist] in
  char '<' <+> hsep slist <+> char '>'

print_doc (EApp e f) =
  let pe = print_doc e
      pf = print_doc f in
  (case e of
     EFun _ _ -> parens pe
     _ -> pe) <+> 
  (case f of
     EFun _ _ -> parens pf
     EApp _ _ -> parens pf
     _ -> pf)

print_doc (EFun p e) =
  text "fun" <+> text (pprint p) <+> text "->" $$
  nest 2 (print_doc e)

print_doc (EIf e f g) =
  text "if" <+> print_doc e <+> text "then" $$
  nest 2 (print_doc f) $$
  text "else" $$
  nest 2 (print_doc g)

print_doc (EBox t) =
  text "box" <> brackets (text $ pprint t)

print_doc EUnbox =
  text "unbox"

print_doc ERev =
  text "rev"

print_doc (EDatacon datacon Nothing) =
  text (subvar 'D' datacon)

print_doc (EDatacon datacon (Just e)) =
  let pe = print_doc e in
  text (subvar 'D' datacon) <+> (case e of
                                   EBool _ -> pe
                                   EUnit -> pe
                                   EVar _ -> pe
                                   _ -> parens pe)

print_doc (EMatch e blist) =
  text "match" <+> print_doc e <+> text "with" $$
  nest 2 (List.foldl (\doc (p, f) ->
                        let pmatch = char '|' <+> text (pprint p) <+> text "->" <+> print_doc e in
                        if isEmpty doc then
                          pmatch
                        else
                          doc $$ pmatch) PP.empty blist)

print_doc (ELocated e _) =
  print_doc e


instance PPrint Expr where
  sprintn lv e = PP.render $ print_doc e
  sprint e = sprintn defaultLvl e
  pprint e = sprintn Inf e



instance PPrint TypeConstraint where
  pprint (Subtype t u) = pprint t ++ " <: " ++ pprint u
  sprintn _ c = pprint c
  sprint c = pprint c


instance PPrint FlagConstraint where
  pprint (m, n) =
    (if m < 2 then
       show m
     else
       subvar 'f' m) ++ " <= " ++
    (if n < 2 then
       show n
     else
       subvar 'f' n)

  sprintn _ c = pprint c
  sprint c = pprint c

instance PPrint ConstraintSet where
  pprint (lcs, fcs) =
    let screenw = 120 in
    let plcs = List.map pprint lcs in
    let maxw = List.maximum $ List.map List.length plcs in
    let nline = screenw `quot` (maxw + 5) in 

    let slcons = fst $ List.foldl (\(s, nth) pc ->
                        let padding = List.take (maxw - List.length pc + 5) $ List.repeat ' ' in

                        if nth == 0 then
                          (s ++ "\n" ++ pc ++ padding, nline)
                        else
                          (s ++ pc ++ padding, nth-1)) ("", nline+1) plcs
    in

    let pfcs = List.map pprint fcs in
    let maxw = List.maximum $ List.map List.length pfcs in
    let nline = screenw `quot` (maxw + 5) in

    let sfcons = fst $ List.foldl (\(s, nth) pc ->
                        let padding = List.take (maxw - List.length pc + 5) $ List.repeat ' ' in

                        if nth == 0 then
                          (s ++ "\n" ++ pc ++ padding, nline)
                        else
                          (s ++ pc ++ padding, nth-1)) ("", nline+1) pfcs
    in

    slcons ++ "\n" ++ sfcons

  sprintn _ cs = pprint cs
  sprint cs = pprint cs
