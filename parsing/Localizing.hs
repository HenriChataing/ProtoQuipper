module Localizing where

data Locus = Loc {
  line :: Int,
  column :: Int
}

instance Eq Locus where
  (==) la lb = line la == line lb && column la == column lb

data Extent = Ext {
  lbegin :: Locus,
  lend :: Locus
}

instance Show Extent where
  show ex =
    if (line $ lbegin ex) == (line $ lend ex) then
      ((show $ line $ lbegin ex) ++ ":" ++
       (show $ column $ lbegin ex) ++ "-" ++
       (show $ column $ lend ex))
    else
      ((show $ line $ lbegin ex) ++ ":" ++
       (show $ column $ lbegin ex) ++ "-" ++
       (show $ line $ lend ex) ++ ":" ++
       (show $ column $ lend ex))

instance Eq Extent where
  (==) exa exb = lbegin exa == lbegin exb && lend exa == lend exb

-- Default locus
locus_unknown :: Locus
---------------------
locus_unknown =
  Loc { line = 0, column = 0 }

-- Default extent
extent_unknown :: Extent
-----------------------
extent_unknown =
  Ext { lbegin = locus_unknown, lend = locus_unknown }

-- Build an extent starting from ex1 and ending at ex2
fromto :: Extent -> Extent -> Extent
------------------------------------
fromto ex1 ex2 =
  Ext { lbegin = Loc { line = line $ lbegin ex1, column = column $ lbegin ex1 },
        lend = Loc { line = line $ lend ex2, column = column $ lend ex2 } }

-- Same as fromto with optional parameters
fromto_opt :: Maybe Extent -> Maybe Extent -> Maybe Extent
---------------------------------------------------------
fromto_opt _ Nothing = Nothing
fromto_opt Nothing _ = Nothing
fromto_opt (Just ex1) (Just ex2) = Just (fromto ex1 ex2)
