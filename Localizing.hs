module Localizing where

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

fromto :: Extent -> Extent -> Extent
fromto ex1 ex2 =
  Ext { lbegin = Loc { file = file $ lbegin ex1, line = line $ lbegin ex1, column = column $ lbegin ex1 },
        lend = Loc { file = file $ lend ex2, line = line $ lend ex2, column = column $ lend ex2 } }

fromtoOpt :: Maybe Extent -> Maybe Extent -> Maybe Extent
fromtoOpt _ Nothing = Nothing
fromtoOpt Nothing _ = Nothing
fromtoOpt (Just ex1) (Just ex2) = Just (fromto ex1 ex2)
