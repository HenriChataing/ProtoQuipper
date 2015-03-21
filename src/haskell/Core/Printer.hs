{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}


-- | This module contains the 'Classes.PPrint' instance declarations of the types 'Type', 'LinType',
-- 'Pattern', and 'Expr' of the /internal syntax/. Please note that instance declarations do not generate
-- any documentation, so there is almost nothing to document here. Please click on \"Source\" to view the
-- source code.
module Core.Printer where

import Utils
import Classes hiding ((<+>))
import Monad.QuipperError
import Core.Syntax hiding ((<>))

import Data.List as List
import Text.PrettyPrint.HughesPJ as PP

-- | Printing of linear types. The generic function 'genprint' parameterizes the printing over the display
-- of flags and type variables.
instance PPrint LinType where
  -- Generic printing. The display of flags and type variables is specified by two option functions
  genprint _ [_, fvar, _] (TVar x) = fvar x
  genprint _ _ (TVar x) = throwNE $ ProgramError "CorePrinter:genprint(LinType): illegal argument"

  genprint _ _ TUnit = "()"
  genprint _ _ TInt = "int"
  genprint _ _ TBool = "bool"
  genprint _ _ TQubit = "qubit"
  
  genprint lv opts@[_, _, fuser] (TAlgebraic n arg) =
    fuser n ++ List.foldr (\t rec -> let prt = genprint lv opts t in
                                    " " ++
                                    (case no_bang t of
                                       TArrow _ _ -> "(" ++ prt ++ ")"
                                       TTensor _ -> "(" ++ prt ++ ")"
                                       TCirc _ _ -> "(" ++ prt ++ ")"
                                       TAlgebraic _ [] -> prt
                                       TAlgebraic _ _ -> "(" ++ prt ++ ")"
                                       _ -> prt) ++ rec) "" arg
  genprint _ _ (TAlgebraic n arg) = throwNE $ ProgramError "CorePrinter:genprint(LinType): illegal argument"
  genprint lv opts@[_, _, fuser] (TSynonym n arg) =
    fuser n ++ List.foldr (\t rec -> let prt = genprint lv opts t in
                                    " " ++
                                    (case no_bang t of
                                       TArrow _ _ -> "(" ++ prt ++ ")"
                                       TTensor _ -> "(" ++ prt ++ ")"
                                       TCirc _ _ -> "(" ++ prt ++ ")"
                                       TAlgebraic _ [] -> prt
                                       TAlgebraic _ _ -> "(" ++ prt ++ ")"
                                       _ -> prt) ++ rec) "" arg
  genprint _ _ (TSynonym n arg) = throwNE $ ProgramError "CorePrinter:genprint(LinType): illegal argument"

  genprint (Nth 0) _ _ = "..."

  genprint lv opts (TTensor (a:rest)) =
    let dlv = decr lv in
    (case a of
       TBang _ (TArrow _ _) -> "(" ++ genprint dlv opts a ++ ")"
       TBang _ (TTensor _) -> "(" ++ genprint dlv opts a ++ ")"
       _ -> genprint dlv opts a) ++
    List.foldl (\s b -> s ++ " * " ++
                  (case b of
                     TBang _ (TArrow _ _) -> "(" ++ genprint dlv opts b ++ ")"
                     TBang _ (TTensor _) -> "(" ++ genprint dlv opts b ++ ")"
                     _ -> genprint dlv opts b )) "" rest
  genprint lv opts (TTensor []) =
    throwNE $ ProgramError "CorePrinter:genprint(LinType): empty tensor"

  genprint lv opts (TArrow a b) =
    let dlv = decr lv in
    (case a of
       TBang _ (TArrow _ _) -> "(" ++ genprint dlv opts a ++ ")"
       _ -> genprint dlv opts a) ++ " -> " ++
    genprint dlv opts b

  genprint lv opts (TCirc a b) =
    let dlv = decr lv in
    "circ(" ++ genprint dlv opts a ++ ", " ++ genprint dlv opts b ++ ")"

  -- Print unto Lvl = n
  -- By default, the flags are printed using the default pprint function
  -- and the variables are displayed as X_n where n is the variable id
  sprintn lv a = genprint lv [pprint, prevar "X", prevar "T"] a



-- | Printing of types. The generic function 'genprint' parameterizes the
-- printing over the display of flag and type variables.
instance PPrint Type where
  -- Generic printing, the options are the same as with linear types
  genprint lv opts@[fflag, _, _] (TBang n a) =
    case (fflag n, a) of
      -- No flag
      ("", _) -> genprint (decr lv) opts a

      -- Flag, check whether parenthesis are necessary
      (f, TArrow _ _) -> f ++ "(" ++ genprint (decr lv) opts a ++ ")"
      (f, TTensor _) -> f ++ "(" ++ genprint (decr lv) opts a ++ ")"
      (f, _) -> f ++ genprint (decr lv) opts a
  genprint lv _ (TBang n a) =
    throwNE $ ProgramError "CorePrinter:genprint(Type): illegal argument"

  -- Print unto Lvl = n
  -- The default functions are the same as with linear types
  sprintn lv a = genprint lv [pprint, prevar "X", prevar "T"] a



-- | Printing of type schemes. The generic function 'genprint'
  -- parameterizes the printing over the display of flag and type
  -- variables.
instance PPrint TypeScheme where
  genprint lv opts (TForall _ [] _ a) =
    genprint lv opts a

  genprint lv opts@[_,fvar,_] (TForall ff fv cset a) =
    "forall" ++ List.foldr (\x s -> " " ++ fvar x ++ s) "" fv ++ ",\n" ++
     genprint Inf opts ((fst cset, []) :: ConstraintSet) ++ "\n => " ++
     genprint lv opts a

  genprint _ _ _ =
    throwNE $ ProgramError "CorePrinter:genprint(TypeScheme): illegal argument"

  sprintn lv a = genprint lv [pprint, prevar "X", prevar "T"] a



-- | Printing of patterns. The function 'genprint' parameterizes the printing over the display of data constructors and term
-- variables.
instance PPrint Pattern where
  -- Generic printing
  -- The functions given as argument indicate how to deal with variables (term variables and datacons)
  genprint _ [fvar, _] (PVar _ x) = fvar x
  genprint _ _ (PVar _ x) =
    throwNE $ ProgramError "CorePrinter:genprint(Pattern): illegal argument"
  genprint _ _ (PUnit _) = "()"
  genprint _ _ (PBool _ b) = if b then "true" else "false"
  genprint _ _ (PInt _ n) = show n
  genprint _ _ (PWildcard _) = "_"
  genprint (Nth 0) _ _ = "..."

  genprint lv opts (PTuple _ (p:rest)) =
    let dlv = decr lv in
    "(" ++ genprint dlv opts p ++
           List.foldl (\s q -> s ++ ", " ++ genprint dlv opts q) "" rest ++ ")"
  genprint lv opts (PTuple _ []) =
    throwNE $ ProgramError "CorePrinter:genprint(Pattern): empty tuple"

  genprint lv opts@[_,fdata] (PDatacon _ dcon p) =
    fdata dcon ++ case p of
                    Just p -> "(" ++ genprint (decr lv) opts p ++ ")"
                    Nothing -> ""
  genprint lv _ (PDatacon _ dcon p) =
    throwNE $ ProgramError "CorePrinter:genprint(Pattern): illegal argument"

  genprint lv opts (PConstraint p _) =
    genprint lv opts p

   -- Print unto Lvl = n
  sprintn lv p = genprint lv [prevar "x", prevar "D"] p


-- * Auxiliary functions

-- | Pretty-print an expression using Hughes's and Peyton Jones's
-- pretty printer combinators. The type 'Doc' is defined in the library
-- "Text.PrettyPrint.HughesPJ" and allows for nested documents.
print_doc :: Lvl                   -- ^ Maximum depth.
          -> Expr                  -- ^ Expression to print.
          -> (Variable -> String)  -- ^ Rendering of term variables.
          -> (Variable -> String)  -- ^ Rendering of data constructors.
          -> Doc                   -- ^ Resulting PP document.
print_doc _ (EUnit _) _ _ =
  text "()"

print_doc _ (EBool _ b) _ _ =
  if b then text "true" else text "false"

print_doc _ (EInt _ n) _ _ =
  text $ show n

print_doc _ (EVar _ x) fvar _ = text $ fvar x

print_doc _ (EGlobal _ x) fvar _ = text $ fvar x

print_doc _ (EBox _ t) _ _=
  text "box" <> brackets (text $ pprint t)

print_doc _ (EUnbox _) _ _ =
  text "unbox"

print_doc _ (ERev _) _ _ =
  text "rev"

print_doc _ (EDatacon _ datacon Nothing) _ fdata =
  text $ fdata datacon

print_doc (Nth 0) _ _ _ =
  text "..."

print_doc lv (ELet r p e f) fvar fdata =
  let dlv = decr lv in
  let recflag = if r == Recursive then text "rec" else empty in
  text "let" <+> recflag <+> text (genprint dlv [fvar, fdata] p) <+> equals <+> print_doc dlv e fvar fdata <+> text "in" $$
  print_doc dlv f fvar fdata

print_doc lv (ETuple _ elist) fvar fdata =
  let dlv = decr lv in
  let plist = List.map (\e -> print_doc dlv e fvar fdata) elist in
  let slist = punctuate comma plist in
  char '(' <> hsep slist <> char ')'

print_doc lv (EApp e f) fvar fdata =
  let dlv = decr lv in
  let pe = print_doc dlv e fvar fdata
      pf = print_doc dlv f fvar fdata in
  (case e of
     EFun _ _ _ -> parens pe
     _ -> pe) <+>
  (case f of
     EFun _ _ _ -> parens pf
     EApp _ _ -> parens pf
     _ -> pf)

print_doc lv (EFun _ p e) fvar fdata =
  let dlv = decr lv in
  text "fun" <+> text (genprint dlv [fvar, fdata] p) <+> text "->" $$
  nest 2 (print_doc dlv e fvar fdata)

print_doc lv (EIf e f g) fvar fdata =
  let dlv = decr lv in
  text "if" <+> print_doc dlv e fvar fdata <+> text "then" $$
  nest 2 (print_doc dlv f fvar fdata) $$
  text "else" $$
  nest 2 (print_doc dlv g fvar fdata)

print_doc lv (EDatacon _ datacon (Just e)) fvar fdata =
  let pe = print_doc (decr lv) e fvar fdata in
  text (fdata datacon) <+> (case e of
                              EBool _ _ -> pe
                              EUnit _ -> pe
                              EVar _ _ -> pe
                              _ -> parens pe)

print_doc lv (EMatch e blist) fvar fdata =
  let dlv = decr lv in
  text "match" <+> print_doc dlv e fvar fdata <+> text "with" $$
  nest 2 (List.foldl (\doc (p, f) ->
                        let pmatch = char '|' <+> text (genprint dlv [fvar, fdata] p) <+> text "->" <+> print_doc dlv f fvar fdata in
                        if isEmpty doc then
                          pmatch
                        else
                          doc $$ pmatch) PP.empty blist)

print_doc lv (EConstraint e _) fvar fdata =
  print_doc lv e fvar fdata

print_doc _ (EError msg) _ _ =
  text "error" <+> text msg



-- | Printing of expressions. The function 'genprint' generalizes the display of term
-- variables and data constructors.
instance PPrint Expr where
  -- Generic printing
  genprint lv [fvar, fdata] e =
    let doc = print_doc lv e fvar fdata in
    PP.render doc
  genprint lv _ e =
    throwNE $ ProgramError "CorePrinter:genprint(Expr): illegal argument"

  -- Other
  -- By default, the term variables are printed as x_n and the data constructors as D_n,
  -- where n is the id of the variable / constructor
  sprintn lv e = genprint lv [prevar "x", prevar "D"] e



-- | Subtyping constraints printing.
instance PPrint TypeConstraint where
  genprint lv opts (Subtype t u _) =
    genprint lv opts t ++ " <: " ++ genprint lv opts u

  genprint lv opts (Sublintype t u _) =
    genprint lv opts t ++ " <: " ++ genprint lv opts u

  sprintn lvl c = genprint Inf [pprint, prevar "x", prevar "T"] c


-- | Printing of flag constraints. The function 'genprint' cannot be parameterized.
instance PPrint FlagConstraint where
  genprint lv [fflag, _, _] (Le m n _) =
    fflag m ++ " <= " ++ fflag n
  genprint lv _ _ =
    throwNE $ ProgramError "CorePrinter:genprint(FlagConstraint): illegal argument"

  sprintn lvl c = genprint lvl [pprint, prevar "X", prevar "T"] c


-- | Printing of constraint sets. The function 'genprint' behaves like the one from the 'PPrint' instance
-- declaration of types and linear types.
instance PPrint ConstraintSet where
  genprint _ opts (lcs, fcs) =
    let screenw = 120 in
    let plcs = List.map (\c -> genprint Inf opts c) lcs in
    let maxw = List.maximum $ List.map List.length plcs in
    let nline = screenw `quot` (maxw + 5) in

    let slcons = fst $ List.foldl (\(s, nth) pc ->
                        let padding = List.take (maxw - List.length pc + 5) $ List.repeat ' ' in

                        if nth == 0 then
                          (s ++ "\n" ++ pc ++ padding, nline)
                        else
                          (s ++ pc ++ padding, nth-1)) ("", nline+1) plcs
    in

    let pfcs = List.map (\c -> genprint Inf opts c) fcs in
    let maxw = List.maximum $ List.map List.length pfcs in
    let nline = screenw `quot` (maxw + 5) in

    let sfcons = fst $ List.foldl (\(s, nth) pc ->
                        let padding = List.take (maxw - List.length pc + 5) $ List.repeat ' ' in

                        if nth == 0 then
                          (s ++ "\n" ++ pc ++ padding, nline)
                        else
                          (s ++ pc ++ padding, nth-1)) ("", nline+1) pfcs
    in

    case (lcs, fcs) of
      ([], []) -> ""
      ([], _) -> sfcons
      (_, []) -> slcons
      _ -> slcons ++ "\n" ++ sfcons

  sprintn lvl cs = genprint lvl [pprint, prevar "X", prevar "T"] cs
