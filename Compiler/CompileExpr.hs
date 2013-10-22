-- | This module defines an intermediary language of the compilation, where patterns have been removed.
module Compiler.CompileExpr where

import Classes
import Utils 

import Parsing.Syntax (RecFlag(..))

import Monad.QuipperError

import Typing.CoreSyntax (Variable, Datacon)

import qualified Data.List as List

import Text.PrettyPrint.HughesPJ as PP


-- | Definition of a set of expressions, where patterns have been removed.
data Expr =
-- STLC
    EVar Variable                                 -- ^ Variable: /x/.
  | EGlobal Variable                              -- ^ Global variable from the imported modules.
  | EFun Variable Expr                            -- ^ Function abstraction: @fun x -> t@.
  | EApp Expr Expr                                -- ^ Function application: @t u@.

-- Introduction of the tensor
  | EUnit                                         -- ^ Unit term: @()@.
  | ETuple [Expr]                                 -- ^ Tuple: @(/t/1, .. , /t//n/)@. By construction, must have /n/ >= 2.
  | ELet RecFlag Variable Expr Expr               -- ^ Let-binding: @let [rec] p = e in f@.
  | ESeq Expr Expr                                -- ^ The expression @e; f@, semantically equivalent to @let _ = e in f@.

-- Custom union types
  | EBool Bool                                    -- ^ Boolean constant: @true@ or @false@.
  | EInt Int                                      -- ^ Integer constant.
  | EIf Expr Expr Expr                            -- ^ Conditional: @if e then f else g@.
  | EDatacon Datacon (Maybe Expr)                 -- ^ Data constructor: @Datacon e@. The argument is optional. The data constructors are considered and manipulated as values.
  | EMatch Expr [(Datacon, Expr)]                 -- ^ Case distinction: @match e with (p1 -> f1 | .. | pn -> fn)@.

-- Quantum rules
  | EBox QType                                    -- ^ The constant @box[T]@.
  | EUnbox QType QType                            -- ^ The constant @unbox@.
  | ERev                                          -- ^ The constant @rev@.

-- Unrelated
  | EBuiltin String                               -- ^ Built-in primitive: @#builtin s@.
  | EAccess Int Variable                          -- ^ Access the nth element of a tuple.
  | ETag Variable                                 -- ^ Return the label of an expression (supposedly a record).
  | EBody Datacon Variable                        -- ^ Return the body of a record that has a known label.
  deriving Show



-- * Printing functions.

-- | Pretty-print an expression using Hughes's and Peyton Jones's
-- pretty printer combinators. The type 'Doc' is defined in the library
-- "Text.PrettyPrint.HughesPJ" and allows for nested documents.
print_doc :: Lvl                   -- ^ Maximum depth.
          -> Expr                  -- ^ Expression to print.
          -> (Variable -> String)  -- ^ Rendering of term variables.
          -> (Variable -> String)  -- ^ Rendering of data constructors.
          -> Doc                   -- ^ Resulting PP document.
print_doc _ (EAccess n v) fvar _ =
  text ("#" ++ show n) <+> text (fvar v)

print_doc _ (ETag v) fvar _ =
  text "LABEL" <+> text (fvar v)

print_doc _ (EBody dcon v) fvar _ =
  text ("EXTRACT_" ++ show dcon) <+> text (fvar v)

print_doc _ EUnit _ _ =
  text "()"

print_doc _ (EBool b) _ _ = 
  if b then text "true" else text "false"

print_doc _ (EInt n) _ _ =
  text $ show n

print_doc _ (EVar x) fvar _ = text $ fvar x

print_doc _ (EGlobal x) fvar _ = text $ fvar x

print_doc _ (EBox n) _ _=
  text "box" <> brackets (text $ show n)

print_doc _ (EUnbox t u) _ _ =
  text $ "unbox(" ++ show t ++ "," ++ show u ++ ")"

print_doc _ ERev _ _ =
  text "rev"

print_doc _ (EDatacon datacon Nothing) _ fdata =
  text $ fdata datacon

print_doc _ (EBuiltin s) _ _=
  text s

print_doc (Nth 0) _ _ _ =
  text "..."

print_doc lv (ESeq e f) fvar fdata =
  (print_doc lv e fvar fdata) <+> text ";" $$
  (print_doc lv f fvar fdata)

print_doc lv (ELet r v e f) fvar fdata =
  let dlv = decr lv in
  let recflag = if r == Recursive then text "rec" else empty in
  text "let" <+> recflag <+> text (fvar v) <+> equals <+> print_doc dlv e fvar fdata <+> text "in" $$
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

print_doc lv (EFun v e) fvar fdata =
  let dlv = decr lv in
  text "fun" <+> text (fvar v) <+> text "->" $$
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
        let pmatch = char '|' <+> text (show p) <+> text "->" <+> print_doc dlv f fvar fdata in
        if isEmpty doc then
          pmatch
        else
          doc $$ pmatch) PP.empty blist)



-- | Printing of expressions. The function 'genprint' generalizes the display of term
-- variables and data constructors.
instance PPrint Expr where
  -- Generic printing
  genprint lv e [fvar, fdata] =
    let doc = print_doc lv e fvar fdata in
    PP.render doc
  genprint lv e _ =
    throwNE $ ProgramError "Preliminaries:genprint(Expr): illegal argument"

  -- Other
  -- By default, the term variables are printed as x_n and the data constructors as D_n,
  -- where n is the id of the variable / constructor
  sprintn lv e = genprint lv e [subvar '%', subvar 'D']
  sprint e = sprintn defaultLvl e
  pprint e = sprintn Inf e


