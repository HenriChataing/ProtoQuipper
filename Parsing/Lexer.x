{
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

-- | This module is automatically generated from the file @Lexer.x@ by Alex, the Haskell lexer generator. It provides the definition of a data type 'Token' of lexical tokens, and a function for lexing a string into a list of tokens.
module Parsing.Lexer (Token(..), mylex) where

import Parsing.Location

import Monad.QuipperError
import Monad.QpState

import qualified Data.List as List
}

%wrapper "posn"

$low_alpha = [a-z]
$up_alpha = [A-Z]
$alpha = [$low_alpha $up_alpha]
$digit = [0-9]
$chars = [$alpha $digit '\_' '\'']
$infix0 = ['\<' '\>' '\|' '\&' '\$' '\=']
$infix1 = ['\@' '\^']
$infix2 = ['\+' '\-']
$infix3 = ['\*' '\/' '\%']
$symbolchar = [$infix0 $infix1 $infix2 $infix3 '\%' '\.' '\:']

tokens :-

  $white+                             ;
  "--".*                              ;
  "{-" ( ~\- | [\r\n] | ( \-+ ( [^\-\}] | [\r\n] ) ) )* \-+\} ;

  "_"                                 { locate_token TkWildcard }
  "<:"                                { locate_token TkSubType }
  "*"                                 { locate_token TkStar }
  "-"                                 { locate_token TkMinus }
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

  \" .* \"                            { \p s -> TkString (posn_to_extent p s, List.init $ List.tail s) }

  and                                 { locate_token TkAnd }
  bool                                { locate_token TkBool }
  box                                 { locate_token TkBox }
  circ                                { locate_token TkCirc }
  else                                { locate_token TkElse }
  error                               { locate_token TkError }
  false                               { locate_token TkFalse }
  fun                                 { locate_token TkFun }
  if                                  { locate_token TkIf }
  import                              { locate_token TkImport }
  in                                  { locate_token TkIn }
  int                                 { locate_token TkInteger }
  let                                 { locate_token TkLet }
  match                               { locate_token TkMatch }
  of                                  { locate_token TkOf }
  qubit                               { locate_token TkQuBit }
  rec                                 { locate_token TkRec }
  rev                                 { locate_token TkRev }
  then                                { locate_token TkThen }
  type                                { locate_token TkType }
  true                                { locate_token TkTrue }
  unbox                               { locate_token TkUnbox }
  val                                 { locate_token TkVal }
  with                                { locate_token TkWith }
  "#builtin"                          { locate_token TkBuiltin }

  $digit+                             { locate_named_token TkInt }
  $up_alpha $chars* \. $low_alpha $chars* { locate_named_token TkQLId }
  $up_alpha $chars* \. $up_alpha $chars*  { locate_named_token TkQUId }
  $low_alpha $chars*                  { locate_named_token TkLId }
  $up_alpha $chars*                   { locate_named_token TkUId }

  $infix0 $symbolchar*                { locate_named_token TkInfix0 }
  $infix1 $symbolchar*                { locate_named_token TkInfix1 } 
  $infix2 $symbolchar*                { locate_named_token TkInfix2 } 
  $infix3 $symbolchar*                { locate_named_token TkInfix3 } 

  [^tokens]                           { locate_named_token TkUnknownToken }

{

-- | Convert Alex's positions to extents.
posn_to_extent :: AlexPosn -> String -> Extent
posn_to_extent (AlexPn p l c) s =
  Ext { lbegin = Loc { line = l, column = c },
        lend = Loc { line = l, column = c+length s-1 },
        file = file_unknown }

-- | The type of lexical tokens. 
-- Each token is annotated with an 'Extent', which records the location of the token
-- in the original file. These extents are later also used to record the location of parsed expressions.
-- The tokens can be divided into five categories: name tokens (variables and data constructors),
-- reserved names, punctuation marks, delimiters, and infix operators.
data Token =
  -- Name tokens: variables and data constructors.
    TkLId (Extent, String)       -- ^ A variable name starting with a lower case character.
  | TkUId (Extent, String)       -- ^ A variable name starting with an upper case character.
  | TkQLId (Extent, String)      -- ^ A qualified lower-case identifier.
  | TkQUId (Extent, String)      -- ^ A qualified upper-case identifier.
  | TkInt (Extent, String)       -- ^ An integer literal. The value of the integer is left unparsed.
  | TkString (Extent, String)    -- ^ A string: a list of characters delimited by double quotes.
  | TkUnknownToken (Extent, String)     -- ^ An error token.

  -- Reserved notations : list of reserved names
  | TkAnd Extent           -- ^ The reserved name \'and'.
  | TkBool Extent          -- ^ The reserved name \'bool'.
  | TkBox Extent           -- ^ The reserved name \'box'.
  | TkCirc Extent          -- ^ The reserved name \'circ'.
  | TkElse Extent          -- ^ The reserved name \'else'.
  | TkError Extent         -- ^ The reserved name \'error\'.
  | TkFalse Extent         -- ^ The reserved name \'false'.
  | TkFun Extent           -- ^ The reserved name \'fun'.
  | TkIf Extent            -- ^ The reserved name \'if'.
  | TkImport Extent        -- ^ The reserved name \'import'.
  | TkIn Extent            -- ^ The reserved name \'in'.
  | TkInteger Extent       -- ^ The reserved name \'int'.
  | TkLet Extent           -- ^ The reserved name \'let'.
  | TkMatch Extent         -- ^ The reserved name \'match'.
  | TkOf Extent            -- ^ The reserved name \'of'. 
  | TkQuBit Extent         -- ^ The reserved name \'qubit'.
  | TkRec Extent           -- ^ The reserved name \'rec'. 
  | TkRev Extent           -- ^ The reserved name \'rev'.
  | TkThen Extent          -- ^ The reserved name \'then'.
  | TkTrue Extent          -- ^ The reserved name \'true'.
  | TkType Extent          -- ^ The reserved name \'type'.
  | TkUnbox Extent         -- ^ The reserved name \'unbox'.
  | TkVal Extent           -- ^ The reserved name \'val'.
  | TkWith Extent          -- ^ The reserved name \'with'. 
  | TkBuiltin Extent       -- ^ The reserved name \'\#builtin'.

  -- Punctuation marks, and other symbols
  | TkWildcard Extent      -- ^ The symbol \'@_@'.
  | TkStar Extent          -- ^ The symbol \'@\*@'.
  | TkMinus Extent         -- ^ The symbol \'@\-@'.
  | TkBar Extent           -- ^ The symbol \'@|@'.
  | TkComma Extent         -- ^ The symbol \'@,@'.
  | TkColon Extent         -- ^ The symbol \'@:@'.
  | TkSemiColon Extent     -- ^ The symbol \'@;@'.
  | TkEq Extent            -- ^ The symbol \'@=@'.
  | TkBang Extent          -- ^ The symbol \'@!@'.
  | TkRArrow Extent        -- ^ The symbol \'@\->@'.
  | TkLArrow Extent        -- ^ The symbol \'@<\-@'.
  | TkSubType Extent       -- ^ The symbol \'@<:@'.
  | TkDblSemiColon Extent  -- ^ The symbol \'@;;@'.
  | TkDot Extent           -- ^ The symbol \'@.@'.
  | TkLArrowStar Extent    -- ^ The symbol \'@<-*@'.

  -- Delimiters
  | TkLParen Extent        -- ^ The delimiter \'@(@'.
  | TkRParen Extent        -- ^ The delimiter \'@)@'.
  | TkLBracket Extent      -- ^ The delimiter \'@\[@'.
  | TkRBracket Extent      -- ^ The delimiter \'@]@'.
  | TkLCurlyBracket Extent -- ^ The delimiter \'@{@'.
  | TkRCurlyBracket Extent -- ^ The delimiter \'@}@'.

  -- Operators
  | TkInfix0 (Extent, String)   -- ^ An operator starting with {\'@\<@', \'@\>@', \'@|@', \'@&@', \'@$@'}, and ending with any sequence of special characters.
  | TkInfix1 (Extent, String)   -- ^ An operator starting with {\'@\@@', \'@^@'}.
  | TkInfix2 (Extent, String)   -- ^ An operator starting with {\'@+@', \'@-@'}.
  | TkInfix3 (Extent, String)   -- ^ An operator starting with {\'@*@', \'@/@'}.


-- | Identify the error token.
is_error :: Token -> Bool
is_error (TkUnknownToken _) = True
is_error _ = False


instance Show Token where
  show (TkLId (ex, s)) = "'" ++ s ++ "' (" ++ show ex ++ ")"
  show (TkUId (ex, s)) = "'" ++ s ++ "' (" ++ show ex ++ ")"
  show (TkQLId (ex, s)) = "'" ++ s ++ "' (" ++ show ex ++ ")"
  show (TkQUId (ex, s)) = "'" ++ s ++ "' (" ++ show ex ++ ")"
  show (TkInt (ex, s)) = "'" ++ s ++ "' (" ++ show ex ++ ")"
  show (TkString (ex,s)) = "'\"" ++ s ++ "\"' (" ++ show ex ++ ")" 
  show (TkUnknownToken (ex, s)) = "'" ++ s ++ "' (" ++ show ex ++ ")"

  show (TkAnd ex) = "'and' (" ++ show ex ++ ")"
  show (TkBool ex) = "'bool' (" ++ show ex ++ ")"
  show (TkBox ex) = "'box' (" ++ show ex ++ ")"
  show (TkCirc ex) = "'circ' (" ++ show ex ++ ")"
  show (TkElse ex) = "'else' (" ++ show ex ++ ")"
  show (TkError ex) = "'error' (" ++ show ex ++ ")"
  show (TkFalse ex) = "'false' (" ++ show ex ++ ")"
  show (TkFun ex) = "'fun' (" ++ show ex ++ ")"
  show (TkIf ex) = "'if' (" ++ show ex ++ ")"
  show (TkImport ex) = "'import' (" ++ show ex ++ ")"
  show (TkIn ex) = "'in' (" ++ show ex ++ ")"
  show (TkInteger ex) = "'int' (" ++ show ex ++ ")"
  show (TkLet ex) = "'let' (" ++ show ex ++ ")"
  show (TkMatch ex) = "'match' (" ++ show ex ++ ")"
  show (TkOf ex) = "'of' (" ++ show ex ++ ")"
  show (TkQuBit ex) = "'qubit' (" ++ show ex ++ ")"
  show (TkRec ex) = "'rec' (" ++ show ex ++ ")"
  show (TkRev ex) = "'rev' (" ++ show ex ++ ")"
  show (TkThen ex) = "'then' (" ++ show ex ++ ")"
  show (TkTrue ex) = "'true' (" ++ show ex ++ ")"
  show (TkType ex) = "'type' (" ++ show ex ++ ")"
  show (TkUnbox ex) = "'unbox' (" ++ show ex ++ ")"
  show (TkVal ex) = "'val' (" ++ show ex ++ ")"
  show (TkWith ex) = "'with' (" ++ show ex ++ ")" 
  show (TkBuiltin ex) = "'#builtin' (" ++ show ex ++ ")"

  show (TkWildcard ex) = "'_' (" ++ show ex ++ ")"
  show (TkStar ex) = "'*' (" ++ show ex ++ ")"
  show (TkMinus ex) = "'-' (" ++ show ex ++ ")"
  show (TkBar ex) = "'|' (" ++ show ex ++ ")"
  show (TkComma ex) = "',' (" ++ show ex ++ ")"
  show (TkColon ex) = "':' (" ++ show ex ++ ")"
  show (TkSemiColon ex) = "';' (" ++ show ex ++ ")"
  show (TkEq ex) = "'=' (" ++ show ex ++ ")"
  show (TkBang ex) = "'!' (" ++ show ex ++ ")"
  show (TkRArrow ex) = "'->' (" ++ show ex ++ ")"
  show (TkLArrow ex) = "'<-' (" ++ show ex ++ ")"
  show (TkSubType ex) = "'<:' (" ++ show ex ++ ")"
  show (TkDblSemiColon ex) = "';;' (" ++ show ex ++ ")"
  show (TkDot ex) = "'.' (" ++ show ex ++ ")"
  show (TkLArrowStar ex) = "'<-*' (" ++ show ex ++ ")"

  -- Delimiters
  show (TkLParen ex) = "'(' (" ++ show ex ++ ")"
  show (TkRParen ex) = "')' (" ++ show ex ++ ")"
  show (TkLBracket ex) = "'[' (" ++ show ex ++ ")"
  show (TkRBracket ex) = "']' (" ++ show ex ++ ")"
  show (TkLCurlyBracket ex) = "'{' (" ++ show ex ++ ")"
  show (TkRCurlyBracket ex) = "'}' (" ++ show ex ++ ")"

  -- Operators
  show (TkInfix0 (ex, s)) = "'" ++ s ++ "' (" ++ show ex ++ ")"
  show (TkInfix1 (ex, s)) = "'" ++ s ++ "' (" ++ show ex ++ ")"
  show (TkInfix2 (ex, s)) = "'" ++ s ++ "' (" ++ show ex ++ ")"
  show (TkInfix3 (ex, s)) = "'" ++ s ++ "' (" ++ show ex ++ ")"

-- | Locate a token. The type signatures matches the one expected of lexing actions.
locate_token :: (Extent -> Token) -> AlexPosn -> String -> Token
locate_token tk p s = tk (posn_to_extent p s)

-- | Same as locate_token, except that the string of the token is also included in the object.
locate_named_token :: ((Extent, String) -> Token) -> AlexPosn -> String -> Token
locate_named_token tk p s = tk (posn_to_extent p s, s)

-- | Change the location file of a token.
locate_token_in_file :: String -> Token -> Token
locate_token_in_file f (TkLId (ex, s)) = TkLId (ex { file = f }, s) 
locate_token_in_file f (TkUId (ex, s)) = TkUId (ex { file = f}, s)
locate_token_in_file f (TkQLId (ex, s)) = TkQLId (ex { file = f }, s)
locate_token_in_file f (TkQUId (ex, s)) = TkQUId (ex { file = f }, s)
locate_token_in_file f (TkInt (ex, s)) = TkInt (ex { file = f }, s)
locate_token_in_file f (TkString (ex, s)) = TkString (ex { file = f }, s)
locate_token_in_file f (TkUnknownToken (ex, s)) = TkUnknownToken (ex { file = f }, s)

locate_token_in_file f (TkAnd ex) = TkAnd ex { file = f }
locate_token_in_file f (TkBool ex) = TkBool ex { file = f }
locate_token_in_file f (TkBox ex) = TkBox ex { file = f }
locate_token_in_file f (TkCirc ex) = TkCirc ex { file = f }
locate_token_in_file f (TkElse ex) = TkElse ex { file = f }
locate_token_in_file f (TkError ex) = TkError ex { file = f }
locate_token_in_file f (TkFalse ex) = TkFalse ex { file = f }
locate_token_in_file f (TkFun ex) = TkFun ex { file = f }
locate_token_in_file f (TkIf ex) = TkIf ex { file = f }
locate_token_in_file f (TkImport ex) = TkImport ex { file = f }
locate_token_in_file f (TkIn ex) = TkIn ex { file = f }
locate_token_in_file f (TkInteger ex) = TkInteger ex { file = f }
locate_token_in_file f (TkLet ex) = TkLet ex { file = f }
locate_token_in_file f (TkMatch ex) = TkMatch ex { file = f }
locate_token_in_file f (TkOf ex) = TkOf ex { file = f }
locate_token_in_file f (TkQuBit ex) = TkQuBit ex { file = f }
locate_token_in_file f (TkRec ex) = TkRec ex { file = f }
locate_token_in_file f (TkRev ex) = TkRev ex { file = f }
locate_token_in_file f (TkThen ex) = TkThen ex { file = f }
locate_token_in_file f (TkTrue ex) = TkTrue ex { file = f }
locate_token_in_file f (TkType ex) = TkType ex { file = f }
locate_token_in_file f (TkUnbox ex) = TkUnbox ex { file = f }
locate_token_in_file f (TkVal ex) = TkVal ex { file = f }
locate_token_in_file f (TkWith ex) = TkWith ex { file = f }
locate_token_in_file f (TkBuiltin ex) = TkBuiltin ex { file = f }

locate_token_in_file f (TkWildcard ex) = TkWildcard ex { file = f }
locate_token_in_file f (TkStar ex) = TkStar ex { file = f }
locate_token_in_file f (TkMinus ex) = TkMinus ex { file = f }
locate_token_in_file f (TkBar ex) = TkBar ex { file = f }
locate_token_in_file f (TkComma ex) = TkComma ex { file = f }
locate_token_in_file f (TkColon ex) = TkColon ex { file = f }
locate_token_in_file f (TkSemiColon ex) = TkSemiColon ex { file = f }
locate_token_in_file f (TkEq ex) = TkEq ex { file = f }
locate_token_in_file f (TkBang ex) = TkBang ex { file = f }
locate_token_in_file f (TkRArrow ex) = TkRArrow ex { file = f }
locate_token_in_file f (TkLArrow ex) = TkLArrow ex { file = f }
locate_token_in_file f (TkSubType ex) = TkSubType ex { file = f }
locate_token_in_file f (TkDblSemiColon ex) = TkDblSemiColon ex { file = f }
locate_token_in_file f (TkDot ex) = TkDot ex { file = f }
locate_token_in_file f (TkLArrowStar ex) = TkLArrowStar ex { file = f }

-- Delimiters
locate_token_in_file f (TkLParen ex) = TkLParen ex { file = f }
locate_token_in_file f (TkRParen ex) = TkRParen ex { file = f }
locate_token_in_file f (TkLBracket ex) = TkLBracket ex { file = f }
locate_token_in_file f (TkRBracket ex) = TkRBracket ex { file = f }
locate_token_in_file f (TkLCurlyBracket ex) = TkLCurlyBracket ex { file = f }
locate_token_in_file f (TkRCurlyBracket ex) = TkRCurlyBracket ex { file = f }

-- Operators
locate_token_in_file f (TkInfix0 (ex, s)) = TkInfix0 (ex { file = f }, s)
locate_token_in_file f (TkInfix1 (ex, s)) = TkInfix1 (ex { file = f }, s)
locate_token_in_file f (TkInfix2 (ex, s)) = TkInfix2 (ex { file = f }, s)
locate_token_in_file f (TkInfix3 (ex, s)) = TkInfix3 (ex { file = f }, s)


-- | Turn an unparsed string into a list of lexical tokens. This is the main lexing function.
-- If the lexer encounters an unrecognized token, it fails with a 'LexicalError' exception.
mylex :: String -> String -> QpState [Token]
mylex filename contents = do
  tokens <- return $ alexScanTokens contents
  tokens <- return $ List.map (locate_token_in_file filename) tokens
  case List.find (\tk -> case tk of
                           TkUnknownToken _ -> True
                           _ -> False) tokens of
    Just (TkUnknownToken (ex, s)) -> throwQ $ LexicalError s ex
    _ -> return tokens 
}
