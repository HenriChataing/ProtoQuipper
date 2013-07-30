-- | This module provides types and functions useful to deal with location in files
-- The location is represented by an extent, which is an interval between two locii

module Parsing.Localizing where


-- | Definition of a locus as a point in a file located
-- by its line and column numbers
data Locus = Loc {
  line :: Int,
  column :: Int
} deriving Eq


-- | Definition of an extent as an interval delimited by two locii
data Extent = Ext {
  lbegin :: Locus,
  lend :: Locus
} deriving Eq


-- | Pretty printing of an extent
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


-- | Default locus : line and column numbers are 0
locus_unknown :: Locus
locus_unknown =
  Loc { line = 0, column = 0 }


-- | Default extent : delimited by the default locus
extent_unknown :: Extent
extent_unknown =
  Ext { lbegin = locus_unknown, lend = locus_unknown }


-- | Return the union of two extents. The extent by be given in an ordered fashion
fromto :: Extent -> Extent -> Extent
fromto ex1 ex2 =
  Ext { lbegin = Loc { line = line $ lbegin ex1, column = column $ lbegin ex1 },
        lend = Loc { line = line $ lend ex2, column = column $ lend ex2 } }


-- | Similar to fromto, but with optional arguments, resulting in
-- an optional result
fromto_opt :: Maybe Extent -> Maybe Extent -> Maybe Extent
fromto_opt _ Nothing = Nothing
fromto_opt Nothing _ = Nothing
fromto_opt (Just ex1) (Just ex2) = Just (fromto ex1 ex2)


-- | Class of objects that can be located in a file
--   locate returns the object located at extent ext
--   locate_opt do the same as locate, with an optional location
--   clear_location removes all location annotations
--   location returns the assiocated location, if any
class Located a where
  locate :: a -> Extent -> a
  locate_opt :: a -> Maybe Extent -> a
  clear_location :: a -> a
  location :: a -> Maybe Extent

