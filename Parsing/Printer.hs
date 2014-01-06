{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

-- | This module contains the 'Classes.PPrint' instance declarations
-- for the types 'Type', 'Pattern', and 'Expr' of the /surface syntax/.
-- Please note that
-- instance declarations do not generate any documentation, so there
-- is almost nothing to document here. Please click on \"Source\" to
-- view the source code.
module Parsing.Printer where

import Classes hiding ((<+>))
import Utils

import Parsing.Syntax

import Text.PrettyPrint.HughesPJ as PP
import Data.List as List

import Monad.QuipperError

instance PPrint Type where
  genprint lv _ t =
    sprintn lv t

  -- Print unto Lvl = n
  sprintn _ TUnit =   "()"
  sprintn _ TBool =   "bool"
  sprintn _ TInt =    "int"
  sprintn _ TQubit =   "qubit"
  sprintn _ (TVar x) = x
  sprintn _ (TQualified m x) = m ++ "." ++ x
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
  sprintn ln (TTensor []) =
    throwNE $ ProgramError "Type:sprintn: empty tensor type"

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

  sprintn lv (TForall a typ) =
    "forall " ++ a ++ "  " ++ sprintn (decr lv) typ

  sprintn lv (TLocated a _) = sprintn lv a

  sprintn lv (TApp a b) =
    let dlv = decr lv in
    sprintn dlv a ++ " " ++ sprintn dlv b





-- * Auxiliary functions

-- | Pretty-print an expression using Hughes's and Peyton Jones's
-- pretty printer combinators. The type 'Doc' is defined in the
-- library "Text.PrettyPrint.HughesPJ" and allows for nested
-- documents.
print_expr :: XExpr -> Doc

print_expr EWildcard = text "_"
print_expr EUnit = text "()"
print_expr (EVar x) = text x
print_expr (EQualified m x) = text m <> text "." <> text x
print_expr ERev = text "rev"
print_expr EUnbox = text "unbox"
print_expr (EBox a) = text "box" <> brackets (text $ pprint a)
print_expr (EBool b) = if b then text "true" else text "false"
print_expr (EInt n) = text $ show n

print_expr (ELet r p e f) =
  let pf = print_expr f
      recflag = if r == Recursive then text "rec" else text "" in
  text "let" <+> recflag <+> text (pprint p) <+> equals <+> print_expr e <+> text "in" $$
  pf

print_expr (ETuple elist) =
  let plist = List.map print_expr elist in
  let slist = punctuate comma plist in
  char '(' <> hsep plist <> char ')'

print_expr (EIf e f g) =
  text "if" <+> print_expr e <+> text "then" $$
  nest 2 (print_expr f) $$
  text "else" $$
  nest 2 (print_expr g)

print_expr (EApp e f) =
  let pe = print_expr e
      pf = print_expr f in
  (case e of
     EIf _ _ _ -> parens pe
     EFun _ _ -> parens pe
     _ -> pe) <+>
  (case f of
     EIf _ _ _ -> parens pf
     EFun _ _ -> parens pf
     EApp _ _ -> parens pf
     _ -> pf)

print_expr (EFun p e) =
  text "fun" <+> text (pprint p) <+> text "->" $$
  nest 4 (print_expr e)

print_expr (EDatacon datacon Nothing) =
  text datacon

print_expr (EDatacon datacon (Just e)) =
  let pe = print_expr e in
  text datacon <+> (case e of
                      EVar _ -> pe
                      EBool _ -> pe
                      EUnit -> pe
                      _ -> parens pe)

print_expr (EMatch e plist) =
  text "match" <+> print_expr e <+> text "with" $$
    nest 2 (List.foldl (\doc (p, f) ->
                          let pmatch = char '|' <+> text (pprint p) <+> text "->" <+> print_expr f in
                          if isEmpty doc then
                            pmatch
                          else
                            doc $$ pmatch) PP.empty plist)


print_expr (EConstraint e t) = print_expr e
print_expr (ELocated e _) = print_expr e
print_expr (EError msg) = text "error" <+> text msg


instance PPrint XExpr where
  genprint lv _ e = sprintn lv e
  sprintn lv e = PP.render $ print_expr e


