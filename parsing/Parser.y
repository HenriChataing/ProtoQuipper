{
module Parser where

import Classes
import Localizing
import QuipperError

import Lexer

import Syntax

import Control.Exception

import Data.Char
import Data.List as List
}

%name parse
%tokentype { Token }
%error { parseError }

%token
  '*' { TkStar $$ }
  ',' { TkComma $$ }
  ':' { TkColon $$ }
  ';' { TkSemiColon $$ }
  '!' { TkBang $$ }
  '|' { TkBar $$ }
  '=' { TkEq $$ }
  '(' { TkLParen $$ }
  ')' { TkRParen $$ }
  '<' { TkLChevron $$ }
  '>' { TkRChevron $$ }
  '[' { TkLBracket $$ }
  ']' { TkRBracket $$ }
  '{' { TkLCurlyBracket $$ }
  '}' { TkRCurlyBracket $$ }  

  FUN { TkFun $$ }
  "->" { TkArrow $$ }
  "<-" { TkBackArrow $$ }
  LET { TkLet $$ }
  IN { TkIn $$ }
  DO { TkDo $$ }

  BOX { TkBox $$ }
  UNBOX { TkUnbox $$ }
  REV { TkRev $$ }
  CIRC { TkCirc $$ }

  IF { TkIf $$ }
  THEN { TkThen $$ }
  ELSE { TkElse $$ }

  MATCH { TkMatch $$ }
  WITH { TkWith $$ }
 
  TRUE { TkTrue $$ }
  FALSE { TkFalse $$ }
  BOOL { TkBool $$ }
  QBIT { TkQBit $$ }

  TYPE { TkType $$ }
  OF { TkOf $$ }

  VAR { TkVar $$ }
  DATACON { TkDatacon $$ }


%left "->"
%nonassoc '*'
%nonassoc '!'

%%

Program :
      Typedef_list Expr                      { ($1, $2) }

Expr :
      FUN Pattern_list "->" Expr             { locate_opt (List.foldr EFun $4 $2) (fromto_opt (Just $1) (location $4)) }
    | IF Expr THEN Expr ELSE Expr            { locate_opt (EIf $2 $4 $6) (fromto_opt (Just $1) (location $6)) }
    | MATCH Expr WITH Matching_list          { EMatch $2 $4 }
    | LET Pattern '=' Expr IN Expr           { locate_opt (ELet $2 $4 $6) (fromto_opt (Just $1) (location $6)) }
    | LET VAR Pattern_list '=' Expr IN Expr  { locate_opt (ELet (PVar (snd $2)) (List.foldr EFun $5 $3) $7) (fromto_opt (Just $1) (location $7)) }
    | DO '{' Do_expr '}'                     { locate $3 (fromto $1 $4) }
    | Apply_expr                             { $1 }

Do_expr :
      Expr "<-" Expr ';' Do_expr         { locate_opt (ELet (pattern_of_expr $1) $3 $5) (fromto_opt (location $1) (location $5)) }
    | Expr ';' Do_expr                   { locate_opt (ELet PUnit $1 $3) (fromto_opt (location $1) (location $3)) }
    | Expr                               { $1 }

Apply_expr :
      Apply_expr Atom_expr               { locate_opt (EApp $1 $2) (fromto_opt (location $1) (location $2)) }
    | DATACON Atom_expr                  { locate_opt (EData (snd $1) $2) (fromto_opt (Just $ fst $1) (location $2)) }
    | Atom_expr                          { $1 }

Atom_expr :
      TRUE                               { locate (EBool True) $1 }
    | FALSE                              { locate (EBool False) $1 }
    | VAR                                { locate (EVar (snd $1)) (fst $1) }
    | BOX '[' ']'                        { locate (EBox TUnit) (fromto $1 $3) }
    | BOX '[' QDataType ']'              { locate (EBox $3) (fromto $1 $4) }
    | UNBOX                              { locate EUnbox $1 }
    | REV                                { locate ERev $1 }
    | '(' Expr ')'                       { $2 }
    | '<' Expr_sep_list '>'              { locate (ETuple $2) (fromto $1 $3) }
    | '<' '>'                            { locate EUnit (fromto $1 $2) }
    | '(' Expr ':' Type ')'              { locate (EConstraint $2 $4) (fromto $1 $5) }


Expr_sep_list :
      Expr ',' Expr                      { [$1, $3] }
    | Expr_sep_list ',' Expr             { $1 ++ [$3] }


Pattern :
      VAR                                { locate (PVar (snd $1)) (fst $1) }
    | '(' Pattern ':' Type ')'           { locate (PConstraint $2 $4) (fromto $1 $5) }
    | '<' Pattern_sep_list '>'           { locate (PTuple $2) (fromto $1 $3) }
    | DATACON Pattern                    { locate_opt (PData (snd $1) $2) (fromto_opt (Just $ fst $1) (location $2)) }
    | '<' '>'                            { locate PUnit (fromto $1 $2) }
    | '(' Pattern ')'                    { $2 }


Pattern_list :
      Pattern                            { [$1] }
    | Pattern Pattern_list               { $1:$2 }


Pattern_sep_list :
      Pattern ',' Pattern                { [$1, $3] }
    | Pattern_sep_list ',' Pattern       { $1 ++ [$3] }


Matching :
      Pattern "->" Expr                  { ($1, $3) }


Matching_list :
      Matching '|' Matching              { [$1, $3] }
    | Matching_list '|' Matching         { $1 ++ [$3] }


Type :
      Tensor_list                               { locate_opt (TTensor $1) (fromto_opt (location $ List.head $1) (location $ List.last $1)) }
    | Type "->" Type                            { locate_opt (TArrow $1 $3) (fromto_opt (location $1) (location $3)) }
    | '!' Type                                  { locate_opt (TBang $2) (fromto_opt (Just $1) (location $2)) }
    | Type_app                                  { $1 }


Type_app :
      Atom_type                                 { $1 }
    | Type_app Atom_type                        { TApp $1 $2 }


Tensor_list :
      Type '*' Type                             { [$1, $3] }
    | Tensor_list '*' Type                      { $1 ++ [$3] }


Atom_type :
      BOOL                                      { locate TBool $1 }
    | QBIT                                      { locate TQBit $1 }
    | VAR                                       { locate (TVar $ snd $1) (fst $1) }
    | '(' ')'                                   { locate TUnit (fromto $1 $2) }
    | CIRC '(' QDataType ',' QDataType ')'      { locate (TCirc $3 $5) (fromto $1 $6) }
    | '(' Type ')'                              { $2 }


QDataType : 
      QBIT                                      { locate TQBit $1 }
    | '(' ')'                                   { locate TUnit (fromto $1 $2) }
    | QData_tensor_list                         { locate_opt (TTensor $1) (fromto_opt (location $ List.head $1) (location $ List.last $1)) }
    | '(' QDataType ')'                         { $2 }


QData_tensor_list :
      QDataType '*' QDataType                   { [$1, $3] }
    | QData_tensor_list '*' QDataType           { $1 ++ [$3] }


Typedef_list :
      {- empty -}                               { [] }
    | Typedef_list Typedef                      { $2:$1 }


Typedef :
      TYPE VAR Var_list '=' Data_intro_list     { Typedef (snd $2) $3 $5 }


Data_intro_list :
      DATACON OF Type                           { [(snd $1, $3)] }
    | Data_intro_list '|' DATACON OF Type       { $1 ++ [(snd $3, $5)] }


Var_list :
      {- empty -}                               { [] }
    | Var_list VAR                              { $1 ++ [snd $2] }

{
parseError :: [Token] -> a
parseError [] = throw $ ParsingError "Unknown"
parseError tokens = throw $ ParsingError (show $ head tokens)
} 
