module Classes where

import Localizing

--------------------------------
-- Class of objects admitting --
-- a pretty printing function --

class PShow a where
  pshow :: a -> String

---------------------------------
-- Class of objects that can   --
-- be assorted with a location --

class Located a where
  locate :: a -> Extent -> a
  locateOpt :: a -> Maybe Extent -> a
  location :: a -> Maybe Extent

--------------------------------
-- Class of objects that can  --
-- have the property of being --
-- atomic                     --

class Atomic a where
  isAtomic :: a -> Bool

--------------------------------
-- Class of objects with type --
-- annotations                --

class Constraint a where
  dropConstraints :: a -> a


---------------------------------
-- Class of reversible objects --

class Reversible a where
  rev :: a -> a


