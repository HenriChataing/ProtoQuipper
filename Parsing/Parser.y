{
module Parsing.Parser where

import Classes

import Parsing.Localizing
import Parsing.Lexer
import Parsing.Syntax

import Monad.QuipperError

import Control.Exception

import Data.Char
import Data.List as List
}

%name parse
%tokentype { Token }
%error { parseError }

%token
  '*' { TkStar $$ }
  '.' { TkDot $$ }
  ',' { TkComma $$ }
  ';' { TkSemiColon $$ }
  '!' { TkBang $$ }
  '|' { TkBar $$ }
  '=' { TkEq $$ }
  '(' { TkLParen $$ }
  ')' { TkRParen $$ }
  '[' { TkLBracket $$ }
  ']' { TkRBracket $$ }

  ";;" { TkDblSemiColon $$ }
  "->" { TkRArrow $$ }
  "<-" { TkLArrow $$ }
  "<-*" { TkLArrowStar $$ }
  "<:" { TkSubType $$ }

  INFIX0 { TkInfix0 $$ }
  INFIX1 { TkInfix1 $$ }
  INFIX2 { TkInfix2 $$ }
  INFIX3 { TkInfix3 $$ }

  BOOL { TkBool $$ }
  BOX { TkBox $$ }
  BUILTIN { TkBuiltin $$ }
  CIRC { TkCirc $$ }
  ELSE { TkElse $$ }
  FALSE { TkFalse $$ }
  FUN { TkFun $$ }
  IF { TkIf $$ }
  IMPORT { TkImport $$ }
  IN { TkIn $$ }
  INTEGER { TkInteger $$ }
  LET { TkLet $$ }
  MATCH { TkMatch $$ }
  QBIT { TkQBit $$ }
  REC { TkRec $$ }
  REV { TkRev $$ }
  THEN { TkThen $$ }
  TRUE { TkTrue $$ }
  TYPE { TkType $$ }
  UNBOX { TkUnbox $$ }
  WITH { TkWith $$ }
  OF { TkOf $$ }

  LID { TkLId $$ }
  UID { TkUId $$ }
  INT { TkInt $$ }

%right "->"
%left INFIX0
%right INFIX1
%left INFIX2
%left INFIX3 '*'
%nonassoc '!'

%%

{- Rules for parsing a program file. The file begins with
  a list of import statements, followed by a list of type definitions.
  The rest of the file must be composed of term declarations
-}

Program :
     Import_list Typedef_list Decl_list          { Prog { imports = $1, typedefs = $2, body = $3, module_name = "", filepath = "" } }


{- List of imported modules
   Module names must begin with an upper case letter
-}
Import_list :
      {- empty -}                                { [] }
    | Import_list IMPORT UID                     { (snd $3):$1 }


{- Algebraic type definitions -}
Typedef_list :
      {- empty -}                                { [] }
    | Typedef_list Typedef                       { $2:$1 }


Typedef :
      TYPE LID Var_list '=' Data_intro_list      { Typedef (snd $2) $3 $5 }


Data_intro_list :
      UID OF Type                               { [(snd $1, Just $3)] }
    | UID                                       { [(snd $1, Nothing)] }
    | Data_intro_list '|' UID OF Type           { $1 ++ [(snd $3, Just $5)] }
    | Data_intro_list '|' UID                   { $1 ++ [(snd $3, Nothing)] }


Var_list :
      {- empty -}                               { [] }
    | Var_list LID                              { $1 ++ [snd $2] }


{- Body of the program : list
  of term declarations, either terms
  of let bindings -}

Decl_list :
      {- empty -}                                { [] }
    | Decl_list Decl                             { $1 ++ [$2] }


Decl :
      LET Pattern '=' Expr ";;"                  { DLet Nonrecursive $2 $4 }
    | LET REC LID Pattern_list '=' Expr ";;"     { DLet Recursive (PVar (snd $3)) (List.foldr EFun $6 $4) }
    | LET LID Pattern_list '=' Expr ";;"         { DLet Nonrecursive (PVar (snd $2)) (List.foldr EFun $5 $3) }
    | Expr ";;"                                  { DExpr $1 }



{- Syntax of expressions : organized as
     Expr
     Seq_expr
     Op_expr
     Apply_epxr
     Atom_expr
-}

Expr :
      FUN Pattern_list "->" Expr                 { locate_opt (List.foldr EFun $4 $2) (fromto_opt (Just $1) (location $4)) }
    | IF Expr THEN Expr ELSE Expr                { locate_opt (EIf $2 $4 $6) (fromto_opt (Just $1) (location $6)) }
    | MATCH Expr WITH Matching_list              { locate_opt (EMatch $2 $4) (fromto_opt (Just $1) (location $ snd $ List.last $4)) }
    | LET Pattern '=' Expr IN Expr               { locate_opt (ELet Nonrecursive $2 $4 $6) (fromto_opt (Just $1) (location $6)) }
    | LET LID Pattern_list '=' Expr IN Expr      { locate_opt (ELet Nonrecursive (PVar (snd $2)) (List.foldr EFun $5 $3) $7) (fromto_opt (Just $1) (location $7)) }
    | LET REC LID Pattern_list '=' Expr IN Expr  { locate_opt (ELet Recursive (PVar (snd $3)) (List.foldr EFun $6 $4) $8) (fromto_opt (Just $1) (location $8)) }
    | Seq_expr                                   { $1 }


Seq_expr :
      Op_expr                                    { $1 }
    | Atom_expr "<-" Op_expr ';' Seq_expr        { locate_opt (ELet Nonrecursive (pattern_of_expr $1) $3 $5) (fromto_opt (location $1) (location $5)) }
    | Atom_expr "<-*" Op_expr ';' Seq_expr       { locate_opt (ELet Nonrecursive (pattern_of_expr $1) (EApp $3 $1) $5) (fromto_opt (location $1) (location $5)) }
    | Op_expr ';' Seq_expr                       { locate_opt (ELet Nonrecursive PUnit $1 $3) (fromto_opt (location $1) (location $3)) }


Op_expr :
      Op_expr INFIX0 Op_expr                     { locate_opt (EApp (EApp (locate (EVar $ snd $2) (fst $2)) $1) $3) (fromto_opt (location $1) (location $3)) }
    | Op_expr INFIX1 Op_expr                     { locate_opt (EApp (EApp (locate (EVar $ snd $2) (fst $2)) $1) $3) (fromto_opt (location $1) (location $3)) }
    | Op_expr INFIX2 Op_expr                     { locate_opt (EApp (EApp (locate (EVar $ snd $2) (fst $2)) $1) $3) (fromto_opt (location $1) (location $3)) }
    | Op_expr INFIX3 Op_expr                     { locate_opt (EApp (EApp (locate (EVar $ snd $2) (fst $2)) $1) $3) (fromto_opt (location $1) (location $3)) }
    | Op_expr '*' Op_expr                        { locate_opt (EApp (EApp (locate (EVar "*") $2) $1) $3) (fromto_opt (location $1) (location $3)) }
    | Apply_expr                                 { $1 }


Infix_op :
      INFIX0                                     { $1 }
    | INFIX1                                     { $1 }
    | INFIX2                                     { $1 }
    | INFIX3                                     { $1 }


Apply_expr :
      Apply_expr Atom_expr                       { locate_opt (EApp $1 $2) (fromto_opt (location $1) (location $2)) }
    | Atom_expr                                  { $1 }


Atom_expr :
      TRUE                                      { locate (EBool True) $1 }
    | FALSE                                     { locate (EBool False) $1 }
    | INT                                       { locate (EInt (read $ snd $1)) (fst $1) }
    | LID                                       { locate (EVar (snd $1)) (fst $1) }
    | BUILTIN LID                               { locate (EBuiltin (snd $2)) (fromto $1 $ fst $2) }
    | BOX '[' ']'                               { locate (EBox TUnit) (fromto $1 $3) }
    | BOX '[' Type ']'                          { locate (EBox $3) (fromto $1 $4) }
    | UNBOX                                     { locate EUnbox $1 }
    | REV                                       { locate ERev $1 }
    | UID '.' LID                               { locate (EQualified (snd $1) (snd $3)) (fromto (fst $1) (fst $3)) }
    | UID                                       { locate (EDatacon (snd $1) Nothing) (fst $1) }
    | '(' ')'                                   { locate EUnit (fromto $1 $2) }
    | '(' Expr ')'                              { $2 }
    | '(' Expr_sep_list ')'                     { locate (ETuple $2) (fromto $1 $3) }
    | '(' Expr "<:" Type ')'                    { locate (EConstraint $2 $4) (fromto $1 $5) }


Expr_sep_list :
      Expr ',' Expr                             { [$1, $3] }
    | Expr_sep_list ',' Expr                    { $1 ++ [$3] }


Pattern :
      LID                                       { locate (PVar (snd $1)) (fst $1) }
    | UID Pattern                               { locate_opt (PDatacon (snd $1) (Just $2)) (fromto_opt (Just $ fst $1) (location $2)) }
    | UID                                       { locate (PDatacon (snd $1) Nothing) (fst $1) }
    | '(' Infix_op ')'                          { locate (PVar (snd $2)) (fst $2) }
    | '(' ')'                                   { locate PUnit (fromto $1 $2) }
    | '(' Pattern ')'                           { $2 }
    | '(' Pattern_sep_list ')'                  { locate (PTuple $2) (fromto $1 $3) }
    | '(' Pattern "<:" Type ')'                 { locate (PConstraint $2 $4) (fromto $1 $5) }


Pattern_list :
      Pattern                                   { [$1] }
    | Pattern Pattern_list                      { $1:$2 }


Pattern_sep_list :
      Pattern ',' Pattern                       { [$1, $3] }
    | Pattern_sep_list ',' Pattern              { $1 ++ [$3] }


Matching :
      Pattern "->" Expr                         { ($1, $3) }


Matching_list :
      Matching '|' Matching                     { [$1, $3] }
    | Matching_list '|' Matching                { $1 ++ [$3] }


{- Definition of types :
   Types are divided in the following categories :
     Type (all)
     Type application
     Tensor Type
     Atom type
-}

Type :
      Tensor_type                               { $1 }
    | Type "->" Type                            { locate_opt (TArrow $1 $3) (fromto_opt (location $1) (location $3)) }
    | '!' Type                                  { locate_opt (TBang $2) (fromto_opt (Just $1) (location $2)) }


Tensor_type :
      Tensor_list                               { case $1 of
                                                    [t] -> t
                                                    _ -> TTensor $ List.reverse $1 }

Tensor_list :
      Type_app                                  { [$1] }
    | Tensor_list '*' Type_app                  { $3:$1 }


Type_app :
      Atom_type                                 { $1 }
    | Type_app Atom_type                        { TApp $1 $2 }


Atom_type :
      BOOL                                      { locate TBool $1 }
    | INTEGER                                   { locate TInt $1 }
    | QBIT                                      { locate TQBit $1 }
    | LID                                       { locate (TVar $ snd $1) (fst $1) }
    | UID '.' LID                               { locate (TQualified (snd $1) (snd $3)) (fromto (fst $1) (fst $3)) }
    | '(' ')'                                   { locate TUnit (fromto $1 $2) }
    | CIRC '(' Type ',' Type ')'                { locate (TCirc $3 $5) (fromto $1 $6) }
    | '(' Type ')'                              { $2 }


{
parseError :: [Token] -> a
parseError [] = throw $ ParsingError "Unknown"
parseError tokens = throw $ ParsingError (show $ head tokens)
} 
