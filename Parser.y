{
module Parser where

import Data.Char
import ParserUtils
import Lexer
import Syntax
}

%name parse
%tokentype { Token }
%error { parseError }

%monad { E } { thenE } { returnE }

%token
  '*' { TkStar $$ }
  ',' { TkComma $$ }
  '!' { TkBang $$ }
  '=' { TkEq $$ }
  '(' { TkLParen $$ }
  ')' { TkRParen $$ }
  '<' { TkLChevron $$ }
  '>' { TkRChevron $$ }
  '[' { TkLBracket $$ }
  ']' { TkRBracket $$ }
  
  FUN { TkFun $$ }
  ARROW { TkArrow $$ }
  VAR { TkVar $$ }
  LET { TkLet $$ }
  IN { TkIn $$ }

  BOX { TkBox $$ }
  UNBOX { TkUnbox $$ }
  REV { TkRev $$ }
  CIRC { TkCirc $$ }

  IF { TkIn $$ }
  THEN { TkThen $$ }
  ELSE { TkElse $$ } 
 
  TRUE { TkTrue $$ }
  FALSE { TkFalse $$ }
  BOOL { TkBool $$ }
  QBIT { TkQBit $$ }

%left ARROW
%left '*'
%nonassoc '!'

%%

Expr : FUN Pattern_list ARROW Expr       { EFun $2 $4 }
     | IF Expr THEN Expr ELSE Expr       { EIf $2 $4 $6 }
     | LET Pattern '=' Expr IN Expr      { ELet $2 $4 $6 }
     | Apply_expr                        { $1 }

Apply_expr : Apply_expr Atom_expr        { EApp $1 $2 }
      | REV Atom_expr                    { ERev $2 }
      | BOX '[' ']' Atom_expr            { EBox TUnit $4 }
      | BOX '[' Type ']' Atom_expr       { EBox $3 $5 }
      | UNBOX Atom_expr                  { EUnbox $2 }
      | Atom_expr                        { $1 }

Atom_expr : '*'                          { locate_expr $1 EEmpty }
     | TRUE                              { locate_expr $1 ETrue }
     | FALSE                             { locate_expr $1 EFalse }
     | VAR                               { locate_expr (fst $1) (EVar (snd $1)) }
     | '(' Expr ')'                      { $2 }
     | '<' Expr ',' Expr '>'             { locate_expr (fromTo $1 $5) (EPair $2 $4) }
     | '(' Expr ',' Expr ',' Expr ')'    { locate_expr (fromTo $1 $7) (ECirc $2 $4 $6) }

Pattern : VAR                            { locate_pattern (fst $1) (PVar (snd $1)) }
        | '<' Pattern ',' Pattern '>'    { locate_pattern (fromTo $1 $5) (PPair $2 $4) }

Pattern_list : Pattern                   { [$1] }
             | Pattern Pattern_list      { $1:$2 }



Atom_type : BOOL                         { locate_type $1 TBool }
          | QBIT                         { locate_type $1 TQBit }
          | CIRC '(' Type ',' Type ')'   { locate_type (fromTo $1 $6) (TCirc $3 $5) }
          | '(' Type ')'                 { $2 }
          | '(' ')'                      { locate_type (fromTo $1 $2) TUnit }

Type : Atom_type                         { $1 }
     | Type '*' Type                     { TTensor $1 $3 }
     | Type ARROW Type                   { TArrow $1 $3 }
     | '!' Type                          { TExp $2 }

{
parseError :: [Token] -> E a
parseError tokens = failE "Parse error"
} 
