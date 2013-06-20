{
module Lexer (Token(..), Locus(..), Extent(..), mylex) where

import Localizing
}

%wrapper "posn"

$low_alpha = [a-z]
$up_alpha = [A-Z]
$alpha = [$low_alpha $up_alpha]
$digit = [0-9]

tokens :-

  $white+                             ;
  "--".*                              ;

  "<:"                                { locate_token TkSubType }
  "*"                                 { locate_token TkStar }
  ","                                 { locate_token TkComma }
  ":"                                 { locate_token TkColon }
  ";"                                 { locate_token TkSemiColon }
  "="                                 { locate_token TkEq }
  "!"                                 { locate_token TkBang }
  "->"                                { locate_token TkArrow }
  "<-"                                { locate_token TkBackArrow }
  "("                                 { locate_token TkLParen } 
  ")"                                 { locate_token TkRParen }
  "<"                                 { locate_token TkLChevron }
  ">"                                 { locate_token TkRChevron }
  "["                                 { locate_token TkLBracket }
  "]"                                 { locate_token TkRBracket }
  "{"                                 { locate_token TkLCurlyBracket }
  "}"                                 { locate_token TkRCurlyBracket }

  bool                                { locate_token TkBool }
  box                                 { locate_token TkBox }
  circ                                { locate_token TkCirc }
  do                                  { locate_token TkDo }
  else                                { locate_token TkElse }
  false                               { locate_token TkFalse }
  fun                                 { locate_token TkFun }
  if                                  { locate_token TkIf }
  in                                  { locate_token TkIn }
  let                                 { locate_token TkLet }
  qbit                                { locate_token TkQBit }
  rev                                 { locate_token TkRev }
  then                                { locate_token TkThen }
  true                                { locate_token TkTrue }
  unbox                               { locate_token TkUnbox }

  $alpha [$alpha $digit]*             { \p s -> TkVar (from_posn p s, s) }
  
{
---------------------------
-- Localization in files --

from_posn :: AlexPosn -> String -> Extent
from_posn (AlexPn p l c) s =
  Ext { lbegin = Loc { line = l, column = c },
        lend = Loc { line = l, column = c+length s-1 }}

---------------------------

data Token =
    TkVar (Extent, String)
  | TkBool Extent     | TkQBit Extent
  | TkBox Extent     | TkUnbox Extent
  | TkCirc Extent
  | TkIf Extent       | TkThen Extent   | TkElse Extent  
  | TkTrue Extent     | TkFalse Extent
  | TkFun Extent      | TkDo Extent
  | TkLet Extent      | TkIn Extent
  | TkRev Extent
  | TkStar Extent
  | TkComma Extent
  | TkColon Extent  | TkSemiColon Extent
  | TkEq Extent
  | TkBang Extent
  | TkArrow Extent  | TkBackArrow Extent
  | TkSubType Extent
  | TkLParen Extent        | TkRParen Extent
  | TkLChevron Extent      | TkRChevron Extent
  | TkLBracket Extent      | TkRBracket Extent
  | TkLCurlyBracket Extent | TkRCurlyBracket Extent

    deriving Show

locate_token :: (Extent -> Token) -> AlexPosn -> String -> Token
locate_token k p s = k (from_posn p s)

mylex :: String -> String -> [Token]
mylex filename contents =
  alexScanTokens contents
}
