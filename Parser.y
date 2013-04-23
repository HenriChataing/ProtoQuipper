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

Term : FUN Pattern_list ARROW Term      { TFun $2 $4 }
     | IF Term THEN Term ELSE Term      { TIf $2 $4 $6 }
     | LET Pattern '=' Term IN Term      { TLet $2 $4 $6 }
     | Apply                            { $1 }

Apply : Apply Atom                      { TApp $1 $2 }
      | REV Atom                        { TRev $2 }
      | BOX '[' ']' Atom                { TBox KUnit $4 }
      | BOX '[' Kind ']' Atom           { TBox $3 $5 }
      | UNBOX Atom                      { TUnbox $2 }
      | Atom                            { $1 }

Atom : '*'                              { TEmpty }
     | TRUE                             { TTrue }
     | FALSE                            { TFalse }
     | VAR                              { TVar $1 }
     | '(' Term ')'                     { $2 }
     | '<' Term ',' Term '>'            { TPair $2 $4 }
     | '(' Term ',' Term ',' Term ')'   { TCirc $2 $4 $6 }

Pattern : VAR                           { PVar $1 }
        | '<' Pattern ',' Pattern '>'   { PPair $2 $4 }

Pattern_list : Pattern                  { [$1] }
             | Pattern Pattern_list     { $1:$2 }

Kind : BOOL                             { KBool }
     | QBIT                             { KQBit }

{
parseError :: Token -> P a
parseError tokens = getLocus `thenP` \(l, c) -> failP ("Parse error : at line " ++ show l)
} 
