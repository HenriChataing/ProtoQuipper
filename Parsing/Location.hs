-- | This module provides types and functions useful to work with location in files.
-- A location is represented by an extent, which is an interval between two loci.
module Parsing.Location where

-- | Definition of a locus as a point in a file located
-- by its line and column numbers.
data Locus = Loc {
  line :: Int,     -- ^ Line number.
  column :: Int    -- ^ Column number.
} deriving Eq


-- | Loci are ordered using the lexical order on pairs (line, column).
instance Ord Locus where
  compare l1 l2 = compare (line l1, column l1) (line l2, column l2)


-- | Definition of an extent as an interval delimited by two loci.
data Extent = Ext {
  lbegin :: Locus,   -- ^ Beginning of the extent.
  lend :: Locus      -- ^ End of the extent.
} deriving Eq


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


-- | Default locus: line and column numbers are set to 0.
locus_unknown :: Locus
locus_unknown =
  Loc { line = 0, column = 0 }


-- | Default extent: delimited by the default locus.
extent_unknown :: Extent
extent_unknown =
  Ext { lbegin = locus_unknown, lend = locus_unknown }



-- | Default file name: \"*Unknown*\"
file_unknown :: String
file_unknown =
  "*Unknown*"


-- | Returns the union of two extents.
fromto :: Extent -> Extent -> Extent
fromto ex1 ex2 =
  let begin = min (lbegin ex1) (lbegin ex2)
      end = max (lend ex1) (lend ex2) in
  Ext { lbegin = begin, lend = end }


-- | Similar to fromto, but with optional arguments, resulting in an optional result.
fromto_opt :: Maybe Extent -> Maybe Extent -> Maybe Extent
fromto_opt _ Nothing = Nothing
fromto_opt Nothing _ = Nothing
fromto_opt (Just ex1) (Just ex2) = Just (fromto ex1 ex2)


-- | Class of objects that can hold locations in files.
class Located a where
  locate :: a -> Extent -> a               -- ^ Annotates an object with a location.
  locate_opt :: a -> Maybe Extent -> a     -- ^ Same as locate, with an optional location.
  clear_location :: a -> a                 -- ^ Removes all location annotations.
  location :: a -> Maybe Extent            -- ^ Returns the location associated to an object, if any.

