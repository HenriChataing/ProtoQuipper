{
-- | Module auto-generated by Alex that performs the lexing of the input files.
-- It contains the definition of the data type Token of tokens, result of the lexing.
module Parsing.Lexer (Token(..), mylex) where

import Parsing.Localizing
}

%wrapper "posn"

$low_alpha = [a-z]
$up_alpha = [A-Z]
$alpha = [$low_alpha $up_alpha]
$digit = [0-9]
$admissible = [_]
$infix0 = ['\<' '\>' '\|' '\&' '\$']
$infix1 = ['\@' '\^']
$infix2 = ['\+' '\-']
$infix3 = ['\*' '\/']
$symbolchar = [$infix0 $infix1 $infix2 $infix3 '\%' '\.' '\:']

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
  "->"                                { locate_token TkRArrow }
  "<-"                                { locate_token TkLArrow }
  "<-*"                               { locate_token TkLArrowStar }
  "("                                 { locate_token TkLParen } 
  ")"                                 { locate_token TkRParen }
  "["                                 { locate_token TkLBracket }
  "]"                                 { locate_token TkRBracket }
  "{"                                 { locate_token TkLCurlyBracket }
  "}"                                 { locate_token TkRCurlyBracket }

  bool                                { locate_token TkBool }
  box                                 { locate_token TkBox }
  circ                                { locate_token TkCirc }
  else                                { locate_token TkElse }
  false                               { locate_token TkFalse }
  fun                                 { locate_token TkFun }
  if                                  { locate_token TkIf }
  import                              { locate_token TkImport }
  in                                  { locate_token TkIn }
  int                                 { locate_token TkInteger }
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
  val                                 { locate_token TkVal }
  with                                { locate_token TkWith }
  "#builtin"                          { locate_token TkBuiltin }

  $digit+                                         { locate_named_token TkInt }
  $low_alpha [$alpha $digit $admissible]*         { locate_named_token TkLId }
  $up_alpha [$up_alpha $digit $admissible]*       { locate_named_token TkLId }
  $up_alpha [$alpha $digit $admissible]*          { locate_named_token TkUId }

  $infix0 $symbolchar*                { locate_named_token TkInfix0 }
  $infix1 $symbolchar*                { locate_named_token TkInfix1 } 
  $infix2 $symbolchar*                { locate_named_token TkInfix2 } 
  $infix3 $symbolchar*                { locate_named_token TkInfix3 } 

{

-- | Converts alex's positions to extents
posn_to_extent :: AlexPosn -> String -> Extent
posn_to_extent (AlexPn p l c) s =
  Ext { lbegin = Loc { line = l, column = c },
        lend = Loc { line = l, column = c+length s-1 }}

-- | Definition of the tokens. 
-- All the tokens are annotated by an extent corresponding to the location of the token
-- in the original file. This will later serve to locate the parsed expressions.
-- The tokens can be separated in four categories : name tokens (variables),
-- punctuation marks, reserved notations, and delimiters.
data Token =
  -- Name tokens : variables and data constructors
    TkLId (Extent, String)       -- ^ Variable names starting with a lower case character.
  | TkUId (Extent, String)       -- ^ Variable names starting with an upper case character.
  | TkInt (Extent, String)       -- ^ Integers. The value of the integer is left unparsed.

  -- Reserved notations : list of reserved names
  | TkBool Extent          -- ^ bool.
  | TkBox Extent           -- ^ box.
  | TkCirc Extent          -- ^ circ.
  | TkElse Extent          -- ^ else.
  | TkFalse Extent         -- ^ false.
  | TkFun Extent           -- ^ fun.
  | TkIf Extent            -- ^ if.
  | TkImport Extent        -- ^ import.
  | TkIn Extent            -- ^ in.
  | TkInteger Extent       -- ^ int.
  | TkLet Extent           -- ^ let.
  | TkMatch Extent         -- ^ match.
  | TkOf Extent            -- ^ of. 
  | TkQBit Extent          -- ^ qbit.
  | TkRec Extent           -- ^ rec. 
  | TkRev Extent           -- ^ rev.
  | TkThen Extent          -- ^ then.
  | TkTrue Extent          -- ^ true.
  | TkType Extent          -- ^ type.
  | TkUnbox Extent         -- ^ unbox.
  | TkVal Extent           -- ^ val.
  | TkWith Extent          -- ^ with. 
  | TkBuiltin Extent       -- ^ \#builtin.

  -- Punctuation marks, and other symbols
  | TkStar Extent          -- ^ \*
  | TkBar Extent           -- ^ |
  | TkComma Extent         -- ^ ,
  | TkColon Extent         -- ^ :
  | TkSemiColon Extent     -- ^ ;
  | TkEq Extent            -- ^ =
  | TkBang Extent          -- ^ !
  | TkRArrow Extent        -- ^ \->
  | TkLArrow Extent        -- ^ <\-
  | TkSubType Extent       -- ^ <:
  | TkDblSemiColon Extent  -- ^ ;;
  | TkDot Extent           -- ^ .
  | TkLArrowStar Extent    -- ^ <-*

  -- Delimiters
  | TkLParen Extent        -- ^ (
  | TkRParen Extent        -- ^ )
  | TkLBracket Extent      -- ^ \[
  | TkRBracket Extent      -- ^ ]
  | TkLCurlyBracket Extent -- ^ {
  | TkRCurlyBracket Extent -- ^ }

  -- Operators
  | TkInfix0 (Extent, String)   -- ^ All operators starting with ['<' '>' | '&' '$'], and ending with any sequence of special characters
  | TkInfix1 (Extent, String)   -- ^ All operators starting with [\@ '^']
  | TkInfix2 (Extent, String)   -- ^ All operators starting with ['+' '-']
  | TkInfix3 (Extent, String)   -- ^ All operators starting with ['*' '/']
    deriving Show

-- | Locate a token. The type signatures matches the one expected of lexing actions.
locate_token :: (Extent -> Token) -> AlexPosn -> String -> Token
locate_token tk p s = tk (posn_to_extent p s)

-- | Same as locate_token, except that the string of the token is also included in the object.
locate_named_token :: ((Extent, String) -> Token) -> AlexPosn -> String -> Token
locate_named_token tk p s = tk (posn_to_extent p s, s)

-- | Lexing function. Inputs an unparsed string, and returns the corresponding list of tokens.
-- The lexer can fail if an recognized token is encountered, in which case it throws a LexicaError exception.
mylex :: String -> IO [Token]
mylex contents =
  return $ alexScanTokens contents
}
