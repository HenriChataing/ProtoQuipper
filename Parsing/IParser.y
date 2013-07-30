{
module IParser where

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
  '.' { TkDot $$ }
  ',' { TkComma $$ }
  '!' { TkBang $$ }
  '(' { TkLParen $$ }
  ')' { TkRParen $$ }

  "->" { TkRArrow $$ }
  "<:" { TkSubType $$ }

  VAL { TkVal $$ }
  
  BOOL { TkBool $$ }
  QBIT { TkQBit $$ }
  CIRC { TkCirc $$ }

  LID { TkLId $$ }
  UID { TkUId $$ }

%right "->"
%nonassoc '*'
%nonassoc '!'

%%

{- Rules for parsing a program file. The file begins with
  a list of import statements, followed by a list of type definitions.
  The rest of the file must be composed of term declarations
-}

Interface :
      Val_list                                  { $1 }


Val_list :
      {- empty -}                               { [] }
    | Val_list Val                              { $2:$1 }


Val :
      VAL LID "<:" Type                         { (snd $2, $4) }


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
    | LID                                       { locate (TVar $ snd $1) (fst $1) }
    | UID '.' LID                               { locate (TQualified (snd $1) (snd $3)) (fromto (fst $1) (fst $3)) }
    | '(' ')'                                   { locate TUnit (fromto $1 $2) }
    | CIRC '(' Type ',' Type ')'                { locate (TCirc $3 $5) (fromto $1 $6) }
    | '(' Type ')'                              { $2 }


{
parseError :: [Token] -> a
parseError [] = throw $ ParsingError "Unknown"
parseError tokens = throw $ ParsingError (show $ head tokens)
} 
