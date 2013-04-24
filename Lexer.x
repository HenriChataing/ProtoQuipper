{
module Lexer (Token(..), Locus(..), Extent(..), alexScanTokens, fromTo, fromToOpt, fromToOptOpt) where
}

%wrapper "posn"

$low_alpha = [a-z]
$up_alpha = [A-Z]
$alpha = [$low_alpha $up_alpha]

tokens :-

  $white+                             ;
  "--".*                              ;

  "*"                                 { locate_token TkStar }
  ","                                 { locate_token TkComma }
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

  $alpha+                             { \p s -> TkVar (from_posn p s, s) }
  
{
---------------------------
-- Localization in files --

data Locus = Loc {
  file :: String,
  line :: Int,
  column :: Int
}

data Extent = Ext {
  lbegin :: Locus,
  lend :: Locus
}

instance Show Extent where
  show ex =
    if (line $ lbegin ex) == (line $ lend ex) then
      ((file $ lbegin ex) ++ ":" ++
        (show $ line $ lbegin ex) ++ ":" ++
        (show $ column $ lbegin ex) ++ "-" ++
        (show $ column $ lend ex))
    else
      ((file $ lbegin ex) ++ ":" ++
        (show $ line $ lbegin ex) ++ ":" ++
        (show $ column $ lbegin ex) ++ "-" ++
        (show $ line $ lend ex) ++ ":" ++
        (show $ column $ lend ex))

fromTo :: Extent -> Extent -> Extent
fromTo ex1 ex2 =
  Ext { lbegin = Loc { file = file $ lbegin ex1, line = line $ lbegin ex1, column = column $ lbegin ex1 },
        lend = Loc { file = file $ lend ex2, line = line $ lend ex2, column = column $ lend ex2 } }

fromToOpt :: Extent -> Maybe Extent -> Maybe Extent
fromToOpt _ Nothing = Nothing
fromToOpt ex1 (Just ex2) = Just (fromTo ex1 ex2)

fromToOptOpt :: Maybe Extent -> Maybe Extent -> Maybe Extent
fromToOptOpt _ Nothing = Nothing
fromToOptOpt Nothing _ = Nothing
fromToOptOpt (Just ex1) (Just ex2) = Just (fromTo ex1 ex2)

from_posn :: AlexPosn -> String -> Extent
from_posn (AlexPn p l c) s =
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
  | TkEq Extent
  | TkBang Extent
  | TkArrow Extent
  | TkLParen Extent   | TkRParen Extent
  | TkLChevron Extent | TkRChevron Extent
  | TkLBracket Extent | TkRBracket Extent
    deriving Show

locate_token :: (Extent -> Token) -> AlexPosn -> String -> Token
locate_token k p s = k (from_posn p s)

}
