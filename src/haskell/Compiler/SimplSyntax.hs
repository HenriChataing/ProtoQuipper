{-# LANGUAGE FlexibleInstances #-}

-- | This module defines an intermediary language of the compilation, where patterns have been removed (SimplSyntax stands for simplified syntax).
module Compiler.SimplSyntax where

import Classes hiding ((<+>))
import Utils

import Monad.Error

import qualified Data.List as List

import Text.PrettyPrint.HughesPJ as PP

-- * Definition of the simplified syntax.

-- | Definition of a set of expressions, where patterns have been removed.
data Expr =
-- STLC
    EVar Variable                                 -- ^ Variable: /x/.
  | EGlobal Variable                              -- ^ Global variable from the imported modules.
  | EFun Variable Expr                            -- ^ Function abstraction: @fun x -> t@.
  | EFix Variable Variable Expr                   -- ^ A recursive function, that binds a name (variable) in its local context.
  | EApp Expr Expr                                -- ^ Function application: @t u@.

-- Introduction of the tensor
  | EUnit                                         -- ^ Unit term: @()@.
  | ETuple [Expr]                                 -- ^ Tuple: @(/t/1, .. , /t//n/)@. By construction, must have /n/ >= 2.
  | ELet Variable Expr Expr                       -- ^ Let-binding: @let p = e in f@. We have no more use for the recursive flag, so it has been dropped.
  | ESeq Expr Expr                                -- ^ The expression @e; f@, semantically equivalent to @let _ = e in f@.

-- Custom union types
  | EBool Bool                                    -- ^ Boolean constant: @true@ or @false@.
  | EInt Int                                      -- ^ Integer constant.
  | EMatch Expr [(Int, Expr)] Expr                -- ^ Case distinction: @match e with (p1 -> f1 | .. | pn -> fn)@. The last expression is the default case.

-- Unrelated
  | EAccess Int Variable                          -- ^ Access the nth element of a tuple.
  | EError String                                 -- ^ Throw an exception.
  deriving Show


-- | The visibility of a declaration. 'External' means accessible outside of the compile unit, and
-- 'Internal' local to the unit.
data Visibility =
    External
  | Internal


instance Show Visibility where
  show External = "external"
  show Internal = "internal"


-- | The top-level declarations of the simplified syntax. The top-level expressions have been eliminated at this point.
data Declaration =
    DLet Visibility Variable Expr                 -- ^ Top level declaration.



-- | Return the list of imported variables of an expression.
imports :: Expr -> [Variable]
imports (EGlobal x) = [x]
imports (EFun _ e) = imports e
imports (EFix _ _ e) = imports e
imports (EApp e f) = List.union (imports e) (imports f)
imports (ETuple elist) = List.nub $ List.concat $ List.map imports elist
imports (ELet _ e f) = List.union (imports e) (imports f)
imports (ESeq e f) = List.union (imports e) (imports f)
imports (EMatch e clist def) = List.union (imports e) $ List.foldl (\imp (n,c) -> List.union (imports c) imp) [] $ (0,def):clist
imports _ = []



-- * Printing functions.

-- | Pretty-print an expression using Hughes's and Peyton Jones's
-- pretty printer combinators. The type 'Doc' is defined in the library
-- "Text.PrettyPrint.HughesPJ" and allows for nested documents.
print_doc :: Lvl                   -- ^ Maximum depth.
          -> Expr                  -- ^ Expression to print.
          -> (Variable -> String)  -- ^ Rendering of term variables.
          -> Doc                   -- ^ Resulting PP document.
print_doc _ (EAccess n v) fvar =
  text ("#" ++ show n) <+> text (fvar v)

print_doc _ EUnit _ =
  text "()"

print_doc _ (EBool b) _ =
  if b then text "true" else text "false"

print_doc _ (EInt n) _ =
  text $ show n

print_doc _ (EVar x) fvar = text $ fvar x

print_doc _ (EGlobal x) fvar = text $ fvar x

print_doc (Nth 0) _ _ =
  text "..."

print_doc lv (ESeq e f) fvar =
  (print_doc lv e fvar) <+> text ";" $$
  (print_doc lv f fvar)

print_doc lv (ELet v e f) fvar =
  let dlv = decr lv in
  text "let" <+> text (fvar v) <+> equals <+> print_doc dlv e fvar <+> text "in" $$
  print_doc dlv f fvar

print_doc lv (ETuple elist) fvar =
  let dlv = decr lv in
  let plist = List.map (\e -> print_doc dlv e fvar) elist in
  let slist = punctuate comma plist in
  char '(' <> hsep slist <> char ')'

print_doc lv (EApp e f) fvar =
  let dlv = decr lv in
  let pe = print_doc dlv e fvar
      pf = print_doc dlv f fvar in
  (case e of
     EFun _ _ -> parens pe
     _ -> pe) <+>
  (case f of
     EFun _ _ -> parens pf
     EApp _ _ -> parens pf
     _ -> pf)

print_doc lv (EFix f x e) fvar =
  let dlv = decr lv in
  text "fun(" <> text (fvar f) <> text ")" <+> text (fvar x) <+> text "->" $$
  nest 2 (print_doc dlv e fvar)

print_doc lv (EFun v e) fvar =
  let dlv = decr lv in
  text "fun" <+> text (fvar v) <+> text "->" $$
  nest 2 (print_doc dlv e fvar)

print_doc lv (EMatch e blist def) fvar =
  let dlv = decr lv in
  text "match" <+> print_doc dlv e fvar <+> text "with" $$
  nest 2 (List.foldl (\doc (p, f) ->
        let pmatch = char '|' <+> text (show p) <+> text "->" <+> print_doc dlv f fvar in
        if isEmpty doc then
          pmatch
        else
          doc $$ pmatch) (text "| def ->" <+> print_doc dlv def fvar)  blist)

print_doc _ (EError msg) _ =
  text ("error " ++ msg)


-- | Printing of expressions. The function 'genprint' generalizes the display of term
-- variables and data constructors.
instance PPrint Expr where
  -- Generic printing
  genprint lv [fvar] e =
    let doc = print_doc lv e fvar in
    PP.render doc
  genprint lv _ e =
    throwNE $ ProgramError "Preliminaries:genprint(Expr): illegal argument"

  -- Other
  -- By default, the term variables are printed as x_n and the data constructors as D_n,
  -- where n is the id of the variable / constructor
  sprintn lv e = genprint lv [prevar "%"] e


instance PPrint [Declaration] where
  genprint lv opts [] =
    ""
  genprint lv [fvar] ((DLet vis x e):ds) =
    let pre = genprint lv [fvar] e in
    let prx = fvar x in
    "let " ++ show vis ++ " " ++ prx ++ " = " ++ pre ++ "\n" ++
    genprint lv [fvar] ds

  genprint _ _ _ =
    throwNE $ ProgramError "Preliminaries:genprint([Declaration]): illegal argument"

  sprintn lv e = genprint lv [prevar "%"] e



