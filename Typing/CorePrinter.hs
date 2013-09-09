{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}


-- | This module contains the 'Classes.PPrint' instance declarations of the types 'Type', 'LinType', 'Pattern', and 'Expr' of the /internal syntax/. Please note that instance declarations do not generate any documentation, so there is almost nothing to document here. Please click on \"Source\" to view the source code.
module Typing.CorePrinter where

import Classes
import Utils
import Monad.QuipperError

import Parsing.Syntax (RecFlag (..))

import Typing.CoreSyntax hiding ((<>))

import Control.Exception
import Data.List as List
import Text.PrettyPrint.HughesPJ as PP

-- | Printing of linear types. The generic function 'genprint' parameterizes the printing
-- over the display of flags and type variables.
instance PPrint LinType where
  -- Generic printing
  -- The display of flags and type variables is specified by two option functions
  genprint _ (TVar x) [_, fvar, _] = fvar x
  genprint _ (TVar x) _ = throw $ ProgramError "LinType:genprint: illegal argument"

  genprint _ TUnit _ = "()"
  genprint _ TInt _ = "int"
  genprint _ TBool _ = "bool"
  genprint _ TQubit _ = "qubit"
  genprint lv (TUser n arg) opts@[_, _, fuser] =
    fuser n ++ List.foldr (\t rec -> let prt = genprint lv t opts in
                                    " " ++
                                    (case no_bang t of
                                       TArrow _ _ -> "(" ++ prt ++ ")"
                                       TTensor _ -> "(" ++ prt ++ ")"
                                       TCirc _ _ -> "(" ++ prt ++ ")"
                                       TUser _ [] -> prt
                                       TUser _ _ -> "(" ++ prt ++ ")"
                                       _ -> prt)) "" arg
  genprint _ (TUser n arg) _ = throw $ ProgramError "LinType:genprint: illegal argument"

  genprint (Nth 0) _ _ = "..."

  genprint lv (TTensor (a:rest)) opts =
    let dlv = decr lv in
    (case a of
       TBang _ (TArrow _ _) -> "(" ++ genprint dlv a opts ++ ")"
       TBang _ (TTensor _) -> "(" ++ genprint dlv a opts ++ ")"
       _ -> genprint dlv a opts) ++
    List.foldl (\s b -> s ++ " * " ++
                  (case b of
                     TBang _ (TArrow _ _) -> "(" ++ genprint dlv b opts ++ ")"
                     TBang _ (TTensor _) -> "(" ++ genprint dlv b opts ++ ")"
                     _ -> genprint dlv b opts)) "" rest
  genprint lv (TTensor []) opts = 
    throw $ ProgramError "LinType:genprint: illegal tensor"

  genprint lv (TArrow a b) opts =
    let dlv = decr lv in
    (case a of
       TBang _ (TArrow _ _) -> "(" ++ genprint dlv a opts ++ ")"
       _ -> genprint dlv a opts) ++ " -> " ++
    genprint dlv b opts

  genprint lv (TCirc a b) opts =
    let dlv = decr lv in
    "circ(" ++ genprint dlv a opts ++ ", " ++ genprint dlv b opts ++ ")"

  -- Print unto Lvl = n
  -- By default, the flags are printed using the default pprint function
  -- and the variables are displayed as X_n where n is the variable id
  sprintn lv a = genprint lv a [pprint, subvar 'X', subvar 'T']

  -- Print unto Lvl = +oo
  pprint a = sprintn Inf a

  -- Print unto Lvl = default
  sprint a = sprintn defaultLvl a


-- | Printing of types. The generic function 'genprint' parameterizes the
-- printing over the display of flag and type variables.
instance PPrint Type where
  -- Generic printing, the options are the same as with linear types
  genprint lv (TBang n a) opts@[fflag, _, _] =
    case (fflag n, a) of
      -- No flag
      ("", _) -> genprint (decr lv) a opts
       
      -- Flag, check whether parenthesis are necessary
      (f, TArrow _ _) -> f ++ "(" ++ genprint (decr lv) a opts ++ ")"
      (f, TTensor _) -> f ++ "(" ++ genprint (decr lv) a opts ++ ")"
      (f, _) -> f ++ genprint (decr lv) a opts
  genprint lv (TBang n a) _ = 
    throw $ ProgramError "Type:genprint: illegal argument"

  genprint lv (TForall ff fv cst a) opts =
    "forall [" ++ show (List.length ff) ++ "] [" ++ show (List.length fv) ++ "], [" ++ show (List.length $ fst cst) ++ "," ++ show (List.length $ snd cst) ++ "] => " ++
     genprint (decr lv) a opts

  -- Print unto Lvl = n
  -- The default functions are the same as with linear types
  sprintn lv a = genprint lv a [pprint, subvar 'X', subvar 'T']
 
  -- Print unto Lvl = +oo
  pprint a = sprintn Inf a

  -- Print unto Lvl = default
  sprint a = sprintn defaultLvl a




-- | Printing of patterns. The function 'genprint' parameterizes the printing over the display of data constructors and term
-- variables.
instance PPrint Pattern where
  -- Generic printing
  -- The functions given as argument indicate how to deal with variables (term variables and datacons)
  genprint _ (PVar x) [fvar, _] =  fvar x
  genprint _ (PVar x) _ =
    throw $ ProgramError "Pattern:genprint: illegal argument"
  genprint _ PUnit _ = "()"
  genprint _ (PBool b) _ = if b then "true" else "false"
  genprint _ (PInt n) _ = show n
  genprint _ PWildcard _ = "_"
  genprint (Nth 0) _ _= "..."

  genprint lv (PTuple (p:rest)) opts =
    let dlv = decr lv in
    "(" ++ genprint dlv p opts ++
           List.foldl (\s q -> s ++ ", " ++ genprint dlv q opts) "" rest ++ ")"
  genprint lv (PTuple []) opts =
    throw $ ProgramError "Pattern:genprint: illegal tuple"

  genprint lv (PDatacon dcon p) opts@[_, fdata] =
    fdata dcon ++ case p of
                    Just p -> "(" ++ genprint (decr lv) p opts ++ ")"
                    Nothing -> ""
  genprint lv (PDatacon dcon p) _ =
    throw $ ProgramError "Pattern:genprint: illegal argument"

  genprint lv (PConstraint p _) opts =
    genprint lv p opts

  genprint lv (PLocated p _) opts =
    genprint lv p opts

   -- Print unto Lvl = n
  sprintn lv p = genprint lv p [subvar 'x', subvar 'D']

  -- Print unto Lvl = +oo
  pprint a = sprintn Inf a

  -- Print unto Lvl = default
  sprint a = sprintn defaultLvl a


-- * Auxiliary functions

-- | Pretty-print an expression using Hughes's and Peyton Jones's
-- pretty printer combinators. The type 'Doc' is defined in the library
-- "Text.PrettyPrint.HughesPJ" and allows for nested documents.
print_doc :: Lvl                   -- ^ Maximum depth.
          -> Expr                  -- ^ Expression to print.
          -> (Variable -> String)  -- ^ Rendering of term variables.
          -> (Variable -> String)  -- ^ Rendering of data constructors.
          -> Doc                   -- ^ Resulting PP document.
print_doc _ EUnit _ _ =
  text "()"

print_doc _ (EBool b) _ _ = 
  if b then text "true" else text "false"

print_doc _ (EInt n) _ _ =
  text $ show n

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
  text "let" <+> recflag <+> text (genprint dlv p [fvar, fdata]) <+> equals <+> print_doc dlv e fvar fdata <+> text "in" $$
  print_doc dlv f fvar fdata

print_doc lv (ETuple elist) fvar fdata =
  let dlv = decr lv in
  let plist = List.map (\e -> print_doc dlv e fvar fdata) elist in
  let slist = punctuate comma plist in
  char '(' <> hsep slist <> char ')'

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
  text "fun" <+> text (genprint dlv p [fvar, fdata]) <+> text "->" $$
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
                        let pmatch = char '|' <+> text (genprint dlv p [fvar, fdata]) <+> text "->" <+> print_doc dlv f fvar fdata in
                        if isEmpty doc then
                          pmatch
                        else
                          doc $$ pmatch) PP.empty blist)

print_doc lv (ELocated e _) fvar fdata =
  print_doc lv e fvar fdata

print_doc lv (EConstraint e _) fvar fdata =
  print_doc lv e fvar fdata



-- | Printing of expressions. The function 'genprint' generalizes the display of term
-- variables and data constructors.
instance PPrint Expr where
  -- Generic printing
  genprint lv e [fvar, fdata] =
    let doc = print_doc lv e fvar fdata in
    PP.render doc
  genprint lv e _ =
    throw $ ProgramError "Expr:genprint: illegal argument"

  -- Other
  -- By default, the term variables are printed as x_n and the data constructors as D_n,
  -- where n is the id of the variable / constructor
  sprintn lv e = genprint lv e [subvar 'x', subvar 'D']
  sprint e = sprintn defaultLvl e
  pprint e = sprintn Inf e



-- | Subtyping constraints printing.
instance PPrint TypeConstraint where
  genprint lv (Subtype t u _) opts =
    genprint lv t opts ++ " <: " ++ genprint lv u opts

  genprint lv (Sublintype t u _) opts =
    genprint lv t opts ++ " <: " ++ genprint lv u opts

  sprintn _ c = pprint c
  sprint c = pprint c
  pprint c = genprint Inf c [pprint, subvar 'x', subvar 'T']


-- | Printing of flag constraints. The function 'genprint' cannot be parameterized.
instance PPrint FlagConstraint where
  pprint (Le m n _) =
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
  genprint _ c _ = pprint c


-- | Printing of constraint sets. The function 'genprint' behaves like the one from the 'PPrint' instance
-- declaration of types and linear types.
instance PPrint ConstraintSet where
  genprint _ (lcs, fcs) opts =
    let screenw = 120 in
    let plcs = List.map (\c -> genprint Inf c opts) lcs in
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
  pprint cs = genprint Inf cs [pprint, subvar 'X', subvar 'T']

