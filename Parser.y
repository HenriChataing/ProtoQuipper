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

Expr : FUN Pattern_list ARROW Expr       { locate_opt (EFun $2 $4) (fromToOpt $1 (location $4)) }
     | IF Expr THEN Expr ELSE Expr       { locate_opt (EIf $2 $4 $6) (fromToOpt $1 (location $6)) }
     | LET Pattern '=' Expr IN Expr      { locate_opt (ELet $2 $4 $6) (fromToOpt $1 (location $6)) }
     | Apply_expr                        { $1 }

Apply_expr : Apply_expr Atom_expr        { locate_opt (EApp $1 $2) (fromToOptOpt (location $1) (location $2)) }
      | REV Atom_expr                    { locate_opt (ERev $2) (fromToOpt $1 (location $2)) }
      | BOX '[' ']' Atom_expr            { locate_opt (EBox TUnit $4) (fromToOpt $1 (location $4)) }
      | BOX '[' Type ']' Atom_expr       { locate_opt (EBox $3 $5) (fromToOpt $1 (location $5)) }
      | UNBOX Atom_expr                  { locate_opt (EUnbox $2) (fromToOpt $1 (location $2)) }
      | Atom_expr                        { $1 }

Atom_expr : '*'                          { locate EEmpty $1 }
     | TRUE                              { locate ETrue $1 }
     | FALSE                             { locate EFalse $1 }
     | VAR                               { locate (EVar (snd $1)) (fst $1) }
     | '(' Expr ')'                      { $2 }
     | '<' Expr ',' Expr '>'             { locate (EPair $2 $4) (fromTo $1 $5) }
     | '(' Expr ',' Expr ',' Expr ')'    { locate (ECirc $2 $4 $6) (fromTo $1 $7) }

Pattern : VAR                            { locate (PVar (snd $1)) (fst $1) }
        | '<' Pattern ',' Pattern '>'    { locate (PPair $2 $4) (fromTo $1 $5) }

Pattern_list : Pattern                   { [$1] }
             | Pattern Pattern_list      { $1:$2 }



Atom_type : BOOL                         { locate TBool $1 }
          | QBIT                         { locate TQBit $1 }
          | CIRC '(' Type ',' Type ')'   { locate (TCirc $3 $5) (fromTo $1 $6) }
          | '(' Type ')'                 { $2 }
          | '(' ')'                      { locate TUnit (fromTo $1 $2) }

Type : Atom_type                         { $1 }
     | Type '*' Type                     { locate_opt (TTensor $1 $3) (fromToOptOpt (location $1) (location $3)) }
     | Type ARROW Type                   { locate_opt (TArrow $1 $3) (fromToOptOpt (location $1) (location $3)) }
     | '!' Type                          { locate_opt (TExp $2) (fromToOpt $1 (location $2)) }

{
parseError :: [Token] -> E a
parseError tokens = failE "Parse error"
} 
