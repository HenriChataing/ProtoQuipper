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

  "*"                                 { locate_token TkStar }
  ","                                 { locate_token TkComma }
  ":"                                 { locate_token TkColon }
  "="                                 { locate_token TkEq }
  "!"                                 { locate_token TkBang }
  "->"                                { locate_token TkArrow }
  "("                                 { locate_token TkLParen } 
  ")"                                 { locate_token TkRParen }
  "<"                                 { locate_token TkLChevron }
  ">"                                 { locate_token TkRChevron }
  "["                                 { locate_token TkLBracket }
  "]"                                 { locate_token TkRBracket }

  bool                                { locate_token TkBool }
  box                                 { locate_token TkBox }
  circ                                { locate_token TkCirc }
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

  $alpha [$alpha $digit]*             { \p s -> TkVar (fromPosn p s, s) }
  
{
---------------------------
-- Localization in files --

fromPosn :: AlexPosn -> String -> Extent
fromPosn (AlexPn p l c) s =
  Ext { lbegin = Loc { file = "*UNKNOWN*", line = l, column = c },
        lend = Loc { file = "*UNKNOWN*", line = l, column = c+length s-1 }}

---------------------------

data Token =
    TkVar (Extent, String)
  | TkBool Extent     | TkQBit Extent
  | TkBox Extent     | TkUnbox Extent
  | TkCirc Extent
  | TkIf Extent       | TkThen Extent   | TkElse Extent  
  | TkTrue Extent     | TkFalse Extent
  | TkFun Extent
  | TkLet Extent      | TkIn Extent
  | TkRev Extent
  | TkStar Extent
  | TkComma Extent
  | TkColon Extent
  | TkEq Extent
  | TkBang Extent
  | TkArrow Extent
  | TkLParen Extent   | TkRParen Extent
  | TkLChevron Extent | TkRChevron Extent
  | TkLBracket Extent | TkRBracket Extent
    deriving Show

locate_token :: (Extent -> Token) -> AlexPosn -> String -> Token
locate_token k p s = k (fromPosn p s)

mylex :: String -> [Token]
mylex = alexScanTokens
}
