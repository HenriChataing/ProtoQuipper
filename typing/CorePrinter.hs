-- | This module provides the pretty printing functions necessary to render
-- the types and expressions of the core syntax

module CorePrinter where

import Classes
import Utils

import Syntax (RecFlag (..))
import CoreSyntax hiding ((<>))

import Text.PrettyPrint.HughesPJ as PP
import Data.List as List

-- | Type printing
instance PPrint LinType where
  -- Print unto Lvl = n
  sprintn lv a = genprint_lintype lv a pprint (\x -> subvar 'X' x)

  -- Print unto Lvl = +oo
  pprint a = sprintn Inf a

  -- Print unto Lvl = default
  sprint a = sprintn defaultLvl a


instance PPrint Type where
  sprintn lv a = genprint_type lv a pprint (\x -> subvar 'X' x)
 
  -- Print unto Lvl = +oo
  pprint a = sprintn Inf a

  -- Print unto Lvl = default
  sprint a = sprintn defaultLvl a


-- | Pretty printing of a lintype
genprint_lintype :: Lvl -> LinType -> (RefFlag -> String) -> (Variable -> String) -> String
genprint_lintype _ (TVar x) _ fvar = fvar x
genprint_lintype _ TUnit _ _ = "T"
genprint_lintype _ TBool _ _ = "bool"
genprint_lintype _ TQbit _ _ = "qbit"
genprint_lintype lv (TUser n arg) fflag fvar = n ++ List.foldr (\t rec -> " " ++ genprint_type lv t fflag fvar ++ rec) "" arg

genprint_lintype (Nth 0) _ _ _ = "..."

genprint_lintype lv (TTensor (a:rest)) fflag fvar =
  let dlv = decr lv in
  (case a of
     TBang _ (TArrow _ _) -> "(" ++ genprint_type dlv a fflag fvar ++ ")"
     TBang _ (TTensor _) -> "(" ++ genprint_type dlv a fflag fvar ++ ")"
     _ -> genprint_type dlv a fflag fvar) ++
  List.foldl (\s b -> s ++ " * " ++
                (case b of
                   TBang _ (TArrow _ _) -> "(" ++ genprint_type dlv b fflag fvar ++ ")"
                   TBang _ (TTensor _) -> "(" ++ genprint_type dlv b fflag fvar ++ ")"
                   _ -> genprint_type dlv b fflag fvar)) "" rest

genprint_lintype lv (TArrow a b) fflag fvar =
  let dlv = decr lv in
  (case a of
     TBang _ (TArrow _ _) -> "(" ++ genprint_type dlv a fflag fvar ++ ")"
     _ -> genprint_type dlv a fflag fvar) ++ " -> " ++
  genprint_type dlv b fflag fvar

genprint_lintype lv (TCirc a b) fflag fvar =
  let dlv = decr lv in
  "circ(" ++ genprint_type dlv a fflag fvar ++ ", " ++ genprint_type dlv b fflag fvar ++ ")"


-- | Same with types
genprint_type :: Lvl -> Type -> (RefFlag -> String) -> (Variable -> String) -> String
genprint_type lv (TBang n a) fflag fvar =
  fflag n ++ genprint_lintype (decr lv) a fflag fvar

genprint_type lv (TForall _ _ _ a) fflag fvar = "forall .. , " ++ genprint_type (decr lv) a fflag fvar




-- | Pretty printing of a pattern
-- The depth limit is given by the level
-- The functions given as argument indicate how to deal with variables (term variables and datacons)
genprint_pattern :: Lvl -> Pattern -> (Variable -> String) -> (Variable -> String) -> String
genprint_pattern _ (PVar x _) fvar _ =  fvar x
genprint_pattern _ PUnit _ _ = "<>"
genprint_pattern (Nth 0) _ _ _= "..."

genprint_pattern lv (PTuple (p:rest)) fvar fdata =
  let dlv = decr lv in
  "<" ++ genprint_pattern dlv p fvar fdata ++
         List.foldl (\s q -> s ++ ", " ++ genprint_pattern dlv q fvar fdata) "" rest ++ ">"

genprint_pattern lv (PDatacon dcon p) fvar fdata =
  fdata dcon ++ case p of
                  Just p -> "(" ++ genprint_pattern (decr lv) p fvar fdata ++ ")"
                  Nothing -> ""

genprint_pattern lv (PConstraint p _) fvar fdata =
  sprintn lv p



instance PPrint Pattern where
   -- Print unto Lvl = n
  sprintn lv p = genprint_pattern lv p (\x -> subvar 'x' x) (\d -> subvar 'D' d)

  -- Print unto Lvl = +oo
  pprint a = sprintn Inf a

  -- Print unto Lvl = default
  sprint a = sprintn defaultLvl a




-- | Print an expression as a pp document
-- Similarly to patterns, this expression is parametrized by two functions
-- describing the behavior of the printer when encountering variables and datacons
print_doc :: Lvl -> Expr -> (Variable -> String) -> (Variable -> String) -> Doc
print_doc _ EUnit _ _ =
  text "<>"

print_doc _ (EBool b) _ _ = 
  if b then text "true" else text "false"

print_doc _ (EVar x) fvar _ = text $ fvar x

print_doc _ (EGlobal x) fvar _ = text $ fvar x

print_doc _ (EBox t) _ _=
  text "box" <> brackets (text $ pprint t)

print_doc _ EUnbox _ _ =
  text "unbox"

print_doc _ ERev _ _ =
  text "rev"

print_doc _ (EDatacon datacon Nothing) _ fdata =
  text $ fdata datacon

print_doc _ (EBuiltin s) _ _=
  text "#builtin" <+> text s

print_doc (Nth 0) _ _ _ =
  text "..."

print_doc lv (ELet r p e f) fvar fdata =
  let dlv = decr lv in
  let recflag = if r == Recursive then text "rec" else empty in
  text "let" <+> recflag <+> text (genprint_pattern dlv p fvar fdata) <+> equals <+> print_doc dlv e fvar fdata <+> text "in" $$
  print_doc dlv f fvar fdata

print_doc lv (ETuple elist) fvar fdata =
  let dlv = decr lv in
  let plist = List.map (\e -> print_doc dlv e fvar fdata) elist in
  let slist = punctuate comma plist in
  char '<' <> hsep slist <> char '>'

print_doc lv (EApp e f) fvar fdata =
  let dlv = decr lv in
  let pe = print_doc dlv e fvar fdata
      pf = print_doc dlv f fvar fdata in
  (case e of
     EFun _ _ -> parens pe
     _ -> pe) <+> 
  (case f of
     EFun _ _ -> parens pf
     EApp _ _ -> parens pf
     _ -> pf)

print_doc lv (EFun p e) fvar fdata =
  let dlv = decr lv in
  text "fun" <+> text (genprint_pattern dlv p fvar fdata) <+> text "->" $$
  nest 2 (print_doc dlv e fvar fdata)

print_doc lv (EIf e f g) fvar fdata =
  let dlv = decr lv in
  text "if" <+> print_doc dlv e fvar fdata <+> text "then" $$
  nest 2 (print_doc dlv f fvar fdata) $$
  text "else" $$
  nest 2 (print_doc dlv g fvar fdata)

print_doc lv (EDatacon datacon (Just e)) fvar fdata =
  let pe = print_doc (decr lv) e fvar fdata in
  text (fdata datacon) <+> (case e of
                              EBool _ -> pe
                              EUnit -> pe
                              EVar _ -> pe
                              _ -> parens pe)

print_doc lv (EMatch e blist) fvar fdata =
  let dlv = decr lv in
  text "match" <+> print_doc dlv e fvar fdata <+> text "with" $$
  nest 2 (List.foldl (\doc (p, f) ->
                        let pmatch = char '|' <+> text (genprint_pattern dlv p fvar fdata) <+> text "->" <+> print_doc dlv e fvar fdata in
                        if isEmpty doc then
                          pmatch
                        else
                          doc $$ pmatch) PP.empty blist)

print_doc lv (ELocated e _) fvar fdata =
  print_doc lv e fvar fdata

print_doc lv (EConstraint e _) fvar fdata =
  print_doc lv e fvar fdata


-- | Same as genprint_pattern
genprint_expr :: Lvl -> Expr -> (Variable -> String) -> (Variable -> String) -> String
genprint_expr lv e fvar fdata =
  let doc = print_doc lv e fvar fdata in
  PP.render doc


instance PPrint Expr where
  sprintn lv e = genprint_expr lv e (\x -> subvar 'x' x) (\d -> subvar 'D' d)
  sprint e = sprintn defaultLvl e
  pprint e = sprintn Inf e




-- | Constraint printing
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
