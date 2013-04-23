{
module Parser where

import Data.Char
import PMonad
import Lexer
import Syntax
}

%name parse
%tokentype { Token }
%error { parseError }

%monad { P } { thenP } { returnP }
%lexer { lexer } { TokenEOF } 

%token
  '*' { TokenEmpty }
  ',' { TokenComma }
  '!' { TokenBang }
  '=' { TokenEq }
  '(' { TokenLParen }
  ')' { TokenRParen }
  '<' { TokenLBracket }
  '>' { TokenRBracket }
  '[' { TokenLBrace }
  ']' { TokenRBrace }
  
  FUN { TokenFun }
  ARROW { TokenArrow }
  VAR { TokenVar $$ }
  LET { TokenLet }
  IN { TokenIn }

  BOX { TokenBox }
  UNBOX { TokenUnbox }
  REV { TokenRev }
  CIRC { TokenCirc }

  IF { TokenIn }
  THEN { TokenThen }
  ELSE { TokenElse } 
 
  TRUE { TokenTrue }
  FALSE { TokenFalse }
  BOOL { TokenBool }
  QBIT { TokenQBit }

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

Atom_expr : '*'                          { EEmpty }
     | TRUE                              { ETrue }
     | FALSE                             { EFalse }
     | VAR                               { EVar $1 }
     | '(' Expr ')'                      { $2 }
     | '<' Expr ',' Expr '>'             { EPair $2 $4 }
     | '(' Expr ',' Expr ',' Expr ')'    { ECirc $2 $4 $6 }

Pattern : VAR                            { PVar $1 }
        | '<' Pattern ',' Pattern '>'    { PPair $2 $4 }

Pattern_list : Pattern                   { [$1] }
             | Pattern Pattern_list      { $1:$2 }

Atom_type : BOOL                         { TBool }
          | QBIT                         { TQBit }
          | CIRC '(' Type ',' Type ')'   { TCirc $3 $5 }
          | '(' Type ')'                 { $2 }
          | '(' ')'                      { TUnit }

Type : Atom_type                         { $1 }
     | Type '*' Type                     { TTensor $1 $3 }
     | Type ARROW Type                   { TArrow $1 $3 }
     | '!' Type                          { TExp $2 }

{
parseError :: Token -> P a
parseError tokens = getLocus `thenP` \(l, c) -> failP ("Parse error : at line " ++ show l)
} 
