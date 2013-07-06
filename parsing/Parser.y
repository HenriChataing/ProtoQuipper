{
module Parser where

import Classes
import Localizing

import Lexer

import Syntax

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
  ARROW { TkArrow $$ }
  BACK_ARROW { TkBackArrow $$ }
  VAR { TkVar $$ }
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
  INJL { TkInjL $$ }
  INJR { TkInjR $$ }
 
  TRUE { TkTrue $$ }
  FALSE { TkFalse $$ }
  BOOL { TkBool $$ }
  QBIT { TkQBit $$ }

%left ARROW
%left '*'
%nonassoc '!'

%%

Expr : FUN Pattern_list ARROW Expr            { locate_opt (List.foldr EFun $4 $2) (fromto_opt (Just $1) (location $4)) }
     | IF Expr THEN Expr ELSE Expr            { locate_opt (EIf $2 $4 $6) (fromto_opt (Just $1) (location $6)) }
     | MATCH Expr WITH Binding_list           { EMatch $2 $4 }
     | LET Pattern '=' Expr IN Expr           { locate_opt (ELet $2 $4 $6) (fromto_opt (Just $1) (location $6)) }
     | LET VAR Pattern_list '=' Expr IN Expr  { locate_opt (ELet (PVar (snd $2)) (List.foldr EFun $5 $3) $7) (fromto_opt (Just $1) (location $7)) }
     | DO '{' Do_expr '}'                     { locate $3 (fromto $1 $4) }
     | Apply_expr                             { $1 }

Do_expr : Expr BACK_ARROW Expr ';' Do_expr { locate_opt (ELet (pattern_of_expr $1) $3 $5) (fromto_opt (location $1) (location $5)) }
        | Expr ';' Do_expr                    { locate_opt (ELet PUnit $1 $3) (fromto_opt (location $1) (location $3)) }
        | Expr                                { $1 }

Apply_expr : Apply_expr Atom_expr        { locate_opt (EApp $1 $2) (fromto_opt (location $1) (location $2)) }
      | UNBOX Atom_expr                  { locate_opt (EUnbox $2) (fromto_opt (Just $1) (location $2)) }
      | INJL Atom_expr                   { locate_opt (EInjL $2) (fromto_opt (Just $1) (location $2)) }
      | INJR Atom_expr                   { locate_opt (EInjR $2) (fromto_opt (Just $1) (location $2)) }
      | Atom_expr                        { $1 }

Atom_expr : '*'                          { locate EUnit $1 }
     | TRUE                              { locate (EBool True) $1 }
     | FALSE                             { locate (EBool False) $1 }
     | VAR                               { locate (EVar (snd $1)) (fst $1) }
     | BOX '[' ']'                       { locate (EBox TUnit) (fromto $1 $3) }
     | BOX '[' Type ']'                  { locate (EBox $3) (fromto $1 $4) }
     | REV                               { locate ERev $1 }
     | '(' Expr ')'                      { $2 }
     | '<' Expr ',' Expr '>'             { locate (EPair $2 $4) (fromto $1 $5) }
     | '<' '>'                           { locate EUnit (fromto $1 $2) }
     | '(' Expr ':' Type ')'             { locate (EConstraint $2 $4) (fromto $1 $5) }

Pattern : VAR                            { locate (PVar (snd $1)) (fst $1) }
        | '(' Pattern ':' Type ')'       { locate (PConstraint $2 $4) (fromto $1 $5) }
        | '<' Pattern ',' Pattern '>'    { locate (PPair $2 $4) (fromto $1 $5) }
        | '<' '>'                        { locate PUnit (fromto $1 $2) }
        | '*'                            { locate PUnit $1 }

Pattern_list : Pattern                   { [$1] }
             | Pattern Pattern_list      { $1:$2 }

Binding : '|' Pattern ARROW Expr         { ($2, $4) }

Binding_list : Binding_list Binding      { $1 ++ [$2] }
             | Binding Binding           { [$1, $2] }

Atom_type : BOOL                         { locate TBool $1 }
          | QBIT                         { locate TQBit $1 }
          | CIRC '(' Type ',' Type ')'   { locate (TCirc $3 $5) (fromto $1 $6) }
          | '(' Type ')'                 { $2 }
          | '(' ')'                      { locate TUnit (fromto $1 $2) }

Type : Atom_type                         { $1 }
     | Type '*' Type                     { locate_opt (TTensor $1 $3) (fromto_opt (location $1) (location $3)) }
     | Type ARROW Type                   { locate_opt (TArrow $1 $3) (fromto_opt (location $1) (location $3)) }
     | '!' Type                          { locate_opt (TExp $2) (fromto_opt (Just $1) (location $2)) }

{
parseError :: [Token] -> a
parseError [] = error "Parse error : unknown token"
parseError tokens = error ("Parse error : on token " ++ (show $ head tokens))
} 
