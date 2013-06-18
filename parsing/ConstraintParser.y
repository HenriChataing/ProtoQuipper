{
module ConstraintParser where

import Classes
import Localizing

import Lexer

import Syntax

import Data.Char
import Data.List as List
}

%name parse_constraints
%tokentype { Token }
%error { parseError }

%token
  '*' { TkStar $$ }
  ',' { TkComma $$ }
  '!' { TkBang $$ }
  '(' { TkLParen $$ }
  ')' { TkRParen $$ }
  "<:" { TkSubType $$ }
  
  ARROW { TkArrow $$ }
  VAR { TkVar $$ }
  CIRC { TkCirc $$ }
  BOOL { TkBool $$ }
  QBIT { TkQBit $$ }

%left ARROW
%left '*'
%nonassoc '!'

%%

Constraint_set : '(' Constraint_list ')'           { $2 }

Constraint_list : Constraint ',' Constraint_list   { $1:$3 }
                | Constraint                       { [$1] }

Constraint : Type "<:" Type              { ($1, $3) }

Atom_type : VAR                          { locate (TVar $ snd $1) $ fst $1 }
          | BOOL                         { locate TBool $1 }
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