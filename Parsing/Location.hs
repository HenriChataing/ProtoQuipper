-- | This module provides types and functions for recording and manipulating locations in files.
-- A location is represented by an /extent/, which is an interval between two loci.
module Parsing.Location where

-- | A /locus/ is a point in a file, identified by its line and column
-- numbers.
data Locus = Loc {
  line :: Int,     -- ^ Line number.
  column :: Int    -- ^ Column number.
} deriving Eq


-- | Loci are ordered using the lexical order on pairs (line, column).
instance Ord Locus where
  compare l1 l2 = compare (line l1, column l1) (line l2, column l2)


-- | An /extent/ is an interval delimited by two loci.
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


-- | The default locus: line and column numbers are set to 0.
locus_unknown :: Locus
locus_unknown =
  Loc { line = 0, column = 0 }


-- | The default extent: delimited by the default locus.
extent_unknown :: Extent
extent_unknown =
  Ext { lbegin = locus_unknown, lend = locus_unknown }


-- | The default file name: @\"*Unknown*\"@.
file_unknown :: String
file_unknown =
  "*Unknown*"


-- | Return the union of two extents.
fromto :: Extent -> Extent -> Extent
fromto ex1 ex2 =
  let begin = min (lbegin ex1) (lbegin ex2)
      end = max (lend ex1) (lend ex2) in
  Ext { lbegin = begin, lend = end }


-- | Like 'fromto', but with optional arguments and an optional result.
fromto_opt :: Maybe Extent -> Maybe Extent -> Maybe Extent
fromto_opt _ Nothing = Nothing
fromto_opt Nothing _ = Nothing
fromto_opt (Just ex1) (Just ex2) = Just (fromto ex1 ex2)


-- | A type class for objects that can be /located/, i.e., annotated with an extent.
class Located a where
  -- | Annotate an object with an extent.
  locate :: a -> Extent -> a
  
  -- | Like 'locate', but the extent is optional.
  locate_opt :: a -> Maybe Extent -> a
  
  -- | Remove all extent annotations.
  clear_location :: a -> a
  
  -- | Return the extent associated with an object, if any.
  location :: a -> Maybe Extent

