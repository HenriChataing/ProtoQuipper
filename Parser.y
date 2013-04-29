{
module Parser where

import Data.Char
import ParserUtils
import Lexer
import Localizing
import Syntax
}

%name parse
%tokentype { Token }
%error { parseError }

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

Expr : FUN Pattern ARROW Expr            { locateOpt (EFun $2 $4) (fromtoOpt (Just $1) (location $4)) }
     | IF Expr THEN Expr ELSE Expr       { locateOpt (EIf $2 $4 $6) (fromtoOpt (Just $1) (location $6)) }
     | LET Pattern '=' Expr IN Expr      { locateOpt (ELet $2 $4 $6) (fromtoOpt (Just $1) (location $6)) }
     | Apply_expr                        { $1 }

Apply_expr : Apply_expr Atom_expr        { locateOpt (EApp $1 $2) (fromtoOpt (location $1) (location $2)) }
      | UNBOX Atom_expr                  { locateOpt (EUnbox $2) (fromtoOpt (Just $1) (location $2)) }
      | Atom_expr                        { $1 }

Atom_expr : '*'                          { locate EEmpty $1 }
     | TRUE                              { locate (EBool True) $1 }
     | FALSE                             { locate (EBool False) $1 }
     | VAR                               { locate (EVar (snd $1)) (fst $1) }
     | BOX '[' ']'                       { locate (EBox TUnit) (fromto $1 $3) }
     | BOX '[' Type ']'                  { locate (EBox $3) (fromto $1 $4) }
     | REV                               { locate ERev $1 }
     | '(' Expr ')'                      { $2 }
     | '<' Expr ',' Expr '>'             { locate (EPair $2 $4) (fromto $1 $5) }
     | '<' '>'                           { locate EEmpty (fromto $1 $2) }
     | '(' Expr ',' Expr ',' Expr ')'    { locate (ECirc $2 $4 $6) (fromto $1 $7) }

Pattern : VAR                            { locate (PVar (snd $1)) (fst $1) }
        | '<' Pattern ',' Pattern '>'    { locate (PPair $2 $4) (fromto $1 $5) }

Atom_type : BOOL                         { locate TBool $1 }
          | QBIT                         { locate TQBit $1 }
          | CIRC '(' Type ',' Type ')'   { locate (TCirc $3 $5) (fromto $1 $6) }
          | '(' Type ')'                 { $2 }
          | '(' ')'                      { locate TUnit (fromto $1 $2) }

Type : Atom_type                         { $1 }
     | Type '*' Type                     { locateOpt (TTensor $1 $3) (fromtoOpt (location $1) (location $3)) }
     | Type ARROW Type                   { locateOpt (TArrow $1 $3) (fromtoOpt (location $1) (location $3)) }
     | '!' Type                          { locateOpt (TExp $2) (fromtoOpt (Just $1) (location $2)) }

{
parseError :: [Token] -> a
parseError tokens = error ("Parse error : on token " ++ (show $ head tokens))
} 
