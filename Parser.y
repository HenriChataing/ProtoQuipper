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

  IF { TokenIn }
  THEN { TokenThen }
  ELSE { TokenElse } 
 
  TRUE { TokenTrue }
  FALSE { TokenFalse }
  BOOL { TokenBool }
  QBIT { TokenQBit }

%%

Term : FUN Pattern_list ARROW Term      { EFun $2 $4 }
     | IF Term THEN Term ELSE Term      { EIf $2 $4 $6 }
     | LET Pattern '=' Term IN Term      { ELet $2 $4 $6 }
     | Apply                            { $1 }

Apply : Apply Atom                      { EApp $1 $2 }
      | REV Atom                        { ERev $2 }
      | BOX '[' ']' Atom                { EBox TUnit $4 }
      | BOX '[' Kind ']' Atom           { EBox $3 $5 }
      | UNBOX Atom                      { EUnbox $2 }
      | Atom                            { $1 }

Atom : '*'                              { EEmpty }
     | TRUE                             { ETrue }
     | FALSE                            { EFalse }
     | VAR                              { EVar $1 }
     | '(' Term ')'                     { $2 }
     | '<' Term ',' Term '>'            { EPair $2 $4 }
     | '(' Term ',' Term ',' Term ')'   { ECirc $2 $4 $6 }

Pattern : VAR                           { PVar $1 }
        | '<' Pattern ',' Pattern '>'   { PPair $2 $4 }

Pattern_list : Pattern                  { [$1] }
             | Pattern Pattern_list     { $1:$2 }

Kind : BOOL                             { TBool }
     | QBIT                             { TQBit }

{
parseError :: Token -> P a
parseError tokens = getLocus `thenP` \(l, c) -> failP ("Parse error : at line " ++ show l)
} 
