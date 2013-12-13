{
  -- | This module is automatically generated from the file @Parser.y@ by Happy,
-- the Haskell parser generator. It provides a function to parse Proto-Quipper module implementations.
module Parsing.Parser (parseError, parse) where

import Classes
import Utils

import Parsing.Location
import Parsing.Lexer
import Parsing.Syntax

import Monad.QuipperError

import Data.Char
import Data.List as List
}

%name parse
%tokentype { Token }
%error { parseError }

%token
  '*' { TkStar $$ }
  '-' { TkMinus $$ }
  '.' { TkDot $$ }
  ',' { TkComma $$ }
  ':' { TkColon $$ }
  ';' { TkSemiColon $$ }
  '!' { TkBang $$ }
  '|' { TkBar $$ }
  '=' { TkEq $$ }
  '(' { TkLParen $$ }
  ')' { TkRParen $$ }
  '[' { TkLBracket $$ }
  ']' { TkRBracket $$ }

  ";;" { TkDblSemiColon $$ }
  "->" { TkRArrow $$ }
  "<-" { TkLArrow $$ }
  "<-*" { TkLArrowStar $$ }
  "<:" { TkSubType $$ }
  "_" { TkWildcard $$ }

  INFIX0 { TkInfix0 $$ }
  INFIX1 { TkInfix1 $$ }
  INFIX2 { TkInfix2 $$ }
  INFIX3 { TkInfix3 $$ }

  AND { TkAnd $$ }
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
  QUBIT { TkQuBit $$ }
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
  QLID { TkQLId $$ }
  INT { TkInt $$ }
  STRING { TkString $$ }
  CHAR { TkChar $$ }

%right "->"
%right ':'
%left INFIX0
%right INFIX1
%left INFIX2 '-'
%left INFIX3 '*'
%nonassoc '!'

%%

{- Rules for parsing a program file. The file begins with
  a list of import statements, followed by a list of type definitions.
  The rest of the file must be composed of term declarations
-}

Program :
     Import_list Decl_list                       { Prog { imports = $1, body = $2, module_name = "", filepath = "", interface = Nothing } }
   | Import_list ";;" Decl_list                  { Prog { imports = $1, body = $3, module_name = "", filepath = "", interface = Nothing } }


{- List of imported modules
   Module names must begin with an upper case letter
-}

Import_list :
      {- empty -}                                { [] }
    | Import_list IMPORT UID                     { (snd $3):$1 }


{- Type definitions:
     Algebraic type
     Synonym type
     Algebraic types can be organized in blocks of co-inductive types
-}

Typedef :
      TYPE LID Var_list '=' Data_intro_list     { Typedef (snd $2) $3 $5 }


Typeblock :
      Typedef                                   { [$1] }
    | Typedef AND Typeblock                     { $1:$3 }


Typesyn :
      TYPE LID Var_list '=' Type                { Typesyn (snd $2) $3 $5 }


Data_intro_list :
      UID OF Type                               { [(snd $1, Just $3)] }
    | UID                                       { [(snd $1, Nothing)] }
    | Data_intro_list '|' UID OF Type           { $1 ++ [(snd $3, Just $5)] }
    | Data_intro_list '|' UID                   { $1 ++ [(snd $3, Nothing)] }


Var_list :
      {- empty -}                               { [] }
    | LID Var_list                              { if List.length (snd $1) == 1 then
                                                    (snd $1):$2
                                                  else
                                                    throwNE $ ParsingError (show $1) }


{- Body of the program : list
  of term declarations, either terms
  of let bindings -}

Decl_list :
      {- empty -}                               { [] }
    | Decl Decl_list                            { $1:$2 }


Decl :
      Typeblock                                            { DTypes $1 }
    | Typeblock ";;"                                       { DTypes $1 }
    | Typesyn                                              { DSyn $1 }
    | Typesyn ";;"                                         { DSyn $1 }
    | LET XExpr '=' XExpr ";;"                             { build_dlet Nonrecursive $2 $4 }
    | LET REC XExpr '=' XExpr ";;"                         { build_dlet Recursive $3 $5 }
    | XExpr ";;"                                           { DExpr $1 }



{- Syntax of x-expressions: organized as
     XExpr
     Seq_XExpr
     Op_XExpr
     Apply_XExpr
     Atom_XExpr
-}

XExpr :
      FUN XExpr_list "->" XExpr                  { locate_opt (multi_EFun $2 $4) (fromto_opt (Just $1) (location $4)) }

    | IF XExpr THEN XExpr ELSE XExpr             { locate_opt (EIf $2 $4 $6) (fromto_opt (Just $1) (location $6)) }
    | MATCH XExpr WITH Matching_list             { locate_opt (EMatch $2 $4) (fromto_opt (Just $1) (location $ snd $ List.last $4)) }
    | LET XExpr '=' XExpr IN XExpr               { flip locate_opt (fromto_opt (Just $1) (location $6)) $
                                                     build_let Nonrecursive $2 $4 $6 }
    | LET REC XExpr '=' XExpr IN XExpr           { flip locate_opt (fromto_opt (Just $1) (location $7)) $
                                                     build_let Recursive $3 $5 $7 }
    | Seq_XExpr                                  { $1 }


Seq_XExpr :
      Op_XExpr                                   { $1 }
    | XExpr "<-" Op_XExpr ';' XExpr              { locate_opt (ELet Nonrecursive $1 $3 $5) (fromto_opt (location $1) (location $5)) }
    | Op_XExpr "<-*" Op_XExpr ';' XExpr          { locate_opt (ELet Nonrecursive $1 (EApp $3 $1) $5) (fromto_opt (location $1) (location $5)) }
    | Op_XExpr ';' XExpr                         { locate_opt (ELet Nonrecursive EWildcard $1 $3) (fromto_opt (location $1) (location $3)) }

Op_XExpr :
      Op_XExpr INFIX0 Op_XExpr                   { locate_opt (EApp (EApp (locate (EVar $ snd $2) (fst $2)) $1) $3) (fromto_opt (location $1) (location $3)) }
    | Op_XExpr INFIX1 Op_XExpr                   { locate_opt (EApp (EApp (locate (EVar $ snd $2) (fst $2)) $1) $3) (fromto_opt (location $1) (location $3)) }
    | Op_XExpr INFIX2 Op_XExpr                   { locate_opt (EApp (EApp (locate (EVar $ snd $2) (fst $2)) $1) $3) (fromto_opt (location $1) (location $3)) }
    | Op_XExpr INFIX3 Op_XExpr                   { locate_opt (EApp (EApp (locate (EVar $ snd $2) (fst $2)) $1) $3) (fromto_opt (location $1) (location $3)) }
    | Op_XExpr ':' Op_XExpr                      { locate_opt (EDatacon "Cons" (Just $ ETuple [$1, $3])) (fromto_opt (location $1) (location $3)) }
    | Op_XExpr '*' Op_XExpr                      { locate_opt (EApp (EApp (locate (EVar "*") $2) $1) $3) (fromto_opt (location $1) (location $3)) }
    | Op_XExpr '-' Op_XExpr                      { locate_opt (EApp (EApp (locate (EVar "-") $2) $1) $3) (fromto_opt (location $1) (location $3)) }
    | Apply_XExpr                                { $1 }


Infix_op :
      INFIX0                                     { $1 }
    | INFIX1                                     { $1 }
    | INFIX2                                     { $1 }
    | '-'                                        { ($1, "-") }
    | INFIX3                                     { $1 }
    | '*'                                        { ($1, "*") }


Apply_XExpr :
      Apply_XExpr Atom_XExpr                     { locate_opt (EApp $1 $2) (fromto_opt (location $1) (location $2)) }
    | '-' Atom_XExpr                             { let negation_symbol = locate (EVar "negation_symbol") (fromto $1 $1) in
                                                   locate_opt (EApp negation_symbol $2) (fromto_opt (Just $1) (location $2)) }
    | Atom_XExpr                                 { $1 }


Atom_XExpr :
      "_"                                       { locate EWildcard $1 }
    | TRUE                                      { locate (EBool True) $1 }
    | FALSE                                     { locate (EBool False) $1 }
    | INT                                       { locate (EInt (read $ snd $1)) (fst $1) }
    | LID                                       { locate (EVar (snd $1)) (fst $1) }
    | UID                                       { locate (EDatacon (snd $1) Nothing) (fst $1) }
    | QLID                                      { let (mname, dot:lid) = List.span (\c -> c /= '.') (snd $1) in
                                                  locate (EQualified mname lid) (fst $1) }
    | CHAR                                      { locate (EDatacon "Char" (Just $ EInt $ ord $ snd $1)) (fst $1) }
    | STRING                                    { locate (List.foldr (\c l ->
                                                                        EDatacon "Cons"
                                                                                 (Just $ ETuple [EDatacon "Char" (Just $ EInt $ ord c), l])) (EDatacon "Nil" Nothing) (snd $1)) (fst $1) }

    | BUILTIN LID                               { locate (EBuiltin (snd $2)) (fromto $1 $ fst $2) }
    | BUILTIN UID                               { locate (EBuiltin (snd $2)) (fromto $1 $ fst $2) }
    | BOX '[' ']'                               { locate (EBox TUnit) (fromto $1 $3) }
    | BOX '[' QType ']'                         { locate (EBox $3) (fromto $1 $4) }
    | UNBOX                                     { locate EUnbox $1 }
    | REV                                       { locate ERev $1 }
    | '(' ')'                                   { locate EUnit (fromto $1 $2) }
    | '(' Infix_op ')'                          { locate (EVar (snd $2)) (fst $2) }
    | '(' XExpr_sep_list ')'                    { case $2 of
                                                    [x] -> x
                                                    _ -> locate (ETuple $2) (fromto $1 $3) }
    | '[' ']'                                   { locate (EDatacon "Nil" Nothing) (fromto $1 $2) }
    | '[' XExpr_sep_list ']'                    { flip locate (fromto $1 $3) $
                                                  List.foldr (\e rest -> EDatacon "Cons" (Just $ ETuple [e,rest])) (EDatacon "Nil" Nothing) $2 }
    | '(' XExpr "<:" Type ')'                   { locate (EConstraint $2 $4) (fromto $1 $5) }

XExpr_sep_list :
      XExpr                                     { [$1] }
    | XExpr ',' XExpr_sep_list                  { $1:$3 }



XExpr_list :
      Atom_XExpr                                { $1 : [] }
    | Atom_XExpr XExpr_list                     { $1 : $2 }




Matching :
      XExpr "->" XExpr                          { ($1, $3) }

Matching_list :
      Matching                                  { [$1] }
    | Matching_list '|' Matching                { $1 ++ [$3] }


{- Definition of types: organized as
     Type
     Tensor_type
     Type_app
     Atom_type
-}

Type :
      Tensor_type                               { $1 }
    | Type "->" Type                            { locate_opt (TArrow $1 $3) (fromto_opt (location $1) (location $3)) }

QType :
      QTensor_type                              { $1 }


Tensor_type :
      Tensor_list                               { case $1 of
                                                    [t] -> t
                                                    _ -> TTensor $ List.reverse $1 }

QTensor_type :
      QTensor_list                              { case $1 of
                                                    [t] -> t
                                                    _ -> TTensor $ List.reverse $1 }

Tensor_list :
      Type_app                                  { [$1] }
    | Tensor_list '*' Type_app                  { $3:$1 }


QTensor_list :
      QAtom_type                                { [$1] }
    | QTensor_list '*' QAtom_type               { $3:$1 }


Type_app :
      Atom_type                                 { $1 }
    | Type_app Atom_type                        { TApp $1 $2 }


Atom_type :
      BOOL                                      { locate TBool $1 }
    | '!' Atom_type                             { locate_opt (bang $2) (fromto_opt (Just $1) (location $2)) }
    | INTEGER                                   { locate TInt $1 }
    | QUBIT                                     { locate TQubit $1 }
    | LID                                       { locate (TVar $ snd $1) (fst $1) }
    | UID '.' LID                               { locate (TQualified (snd $1) (snd $3)) (fromto (fst $1) (fst $3)) }
    | '(' ')'                                   { locate TUnit (fromto $1 $2) }
    | CIRC '(' Type ',' Type ')'                { locate (TCirc $3 $5) (fromto $1 $6) }
    | '(' Type ')'                              { $2 }


QAtom_type :
      QUBIT                                     { locate TQubit $1 }
    | '(' ')'                                   { locate TUnit (fromto $1 $2) }
    | '(' QType ')'                             { $2 }



{

-- | Take a list of tokens, and returns the parsed program. This is the main parsing function for module implementation files.
parse :: [Token] -> Program

-- | This function is called by the parser when it comes across an unexpected sequence of tokens.
-- The argument holds the list of remaining tokens. If this list is empty, the error
-- is \'Unexpected end of file\'; this occurs when the parser encounters an incomplete expression. Otherwise, the head corresponds to the location where
-- the parsing failed.
parseError :: [Token] -> a
parseError [] = throwNE EndOfFileError
parseError tokens = throwNE $ ParsingError (show $ head tokens)
}
