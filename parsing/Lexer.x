{
module Lexer (Token(..), Locus(..), Extent(..), mylex) where

import Localizing
}

%wrapper "posn"

$low_alpha = [a-z]
$up_alpha = [A-Z]
$alpha = [$low_alpha $up_alpha]
$digit = [0-9]

$lid = $low_alpha [$alpha $digit]*
$uid = $up_alpha [$alpha $digit]*

tokens :-

  $white+                             ;
  "--".*                              ;

  "<:"                                { locate_token TkSubType }
  "*"                                 { locate_token TkStar }
  "."                                 { locate_token TkDot }
  ","                                 { locate_token TkComma }
  ":"                                 { locate_token TkColon }
  ";"                                 { locate_token TkSemiColon }
  ";;"                                { locate_token TkDblSemiColon }
  "="                                 { locate_token TkEq }
  "!"                                 { locate_token TkBang }
  "|"                                 { locate_token TkBar }
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
  import                              { locate_token TkImport }
  in                                  { locate_token TkIn }
  let                                 { locate_token TkLet }
  match                               { locate_token TkMatch }
  of                                  { locate_token TkOf }
  qbit                                { locate_token TkQBit }
  rec                                 { locate_token TkRec }
  rev                                 { locate_token TkRev }
  then                                { locate_token TkThen }
  type                                { locate_token TkType }
  true                                { locate_token TkTrue }
  unbox                               { locate_token TkUnbox }
  with                                { locate_token TkWith }

  $lid                                { locate_named_token TkLId }
  $up_alpha [$up_alpha $digit]*       { locate_named_token TkLId }
  $uid                                { locate_named_token TkUId }

{

-- | Converts alex's positions to extents
posn_to_extent :: AlexPosn -> String -> Extent
posn_to_extent (AlexPn p l c) s =
  Ext { lbegin = Loc { line = l, column = c },
        lend = Loc { line = l, column = c+length s-1 }}

-- | List of the tokens
-- All the tokens are annotated by an extent, which is the location of the token
-- in the original file. This will later serve to locate the expressions parsed

data Token =
  -- Name tokens : variables and data constructors
    TkLId (Extent, String)
  | TkUId (Extent, String)

  -- Reserved notations : list of reserved names
  | TkBool Extent          | TkQBit Extent
  | TkBox Extent           | TkUnbox Extent
  | TkCirc Extent          | TkIf Extent
  | TkThen Extent          | TkElse Extent
  | TkMatch Extent         | TkWith Extent
  | TkTrue Extent          | TkFalse Extent
  | TkFun Extent           | TkDo Extent
  | TkLet Extent           | TkIn Extent
  | TkRev Extent           | TkType Extent
  | TkOf Extent            | TkRec Extent
  | TkImport Extent

  -- Punctuation marks, and other symbols
  | TkStar Extent          | TkBar Extent
  | TkComma Extent         | TkColon Extent
  | TkSemiColon Extent     | TkEq Extent
  | TkBang Extent          | TkArrow Extent
  | TkBackArrow Extent     | TkSubType Extent
  | TkDblSemiColon Extent  | TkDot Extent

  -- Delimiters
  | TkLParen Extent        | TkRParen Extent
  | TkLChevron Extent      | TkRChevron Extent
  | TkLBracket Extent      | TkRBracket Extent
  | TkLCurlyBracket Extent | TkRCurlyBracket Extent
    deriving Show

-- | Locate a token. The type signatures matches the one expected of lexing actions
locate_token :: (Extent -> Token) -> AlexPosn -> String -> Token
locate_token tk p s = tk (posn_to_extent p s)

-- | Same as locate_token, except that the string of the token is also included in the object
locate_named_token :: ((Extent, String) -> Token) -> AlexPosn -> String -> Token
locate_named_token tk p s = tk (posn_to_extent p s, s)

-- | Lexing function
mylex :: String -> String -> IO [Token]
mylex filename contents =
  return $ alexScanTokens contents
}
