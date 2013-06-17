-- This module provides several custom class definitions
module Classes where

import Localizing

--------------------------------
-- Class defining printing    --
-- functions                  --

-- Recursion level (depth of tree)
data Lvl = Nth Int | Inf
incr :: Lvl -> Lvl
incr (Nth n) = Nth (n+1)
incr Inf = Inf

decr :: Lvl -> Lvl
decr (Nth n) = Nth (n-1)
decr Inf = Inf

-- Default printing level
defaultLvl = Nth 2

-- Pretty printing
class PPrint a where
  -- Print until Lvl = n
  sprintn :: Lvl -> a -> String
  -- Shortened printing : Lvl = default
  sprint  :: a -> String
  -- Pretty printing : Lvl = +oo
  pprint :: a -> String

---------------------------------
-- Class of objects that can   --
-- be assorted with a location --

class Located a where
  locate :: a -> Extent -> a
  locate_opt :: a -> Maybe Extent -> a
  clear_location :: a -> a
  location :: a -> Maybe Extent

--------------------------------
-- Class of objects that can  --
-- have the property of being --
-- atomic                     --

class Atomic a where
  is_atomic :: a -> Bool

--------------------------------
-- Class of objects with type --
-- annotations                --

class Constraint a where
  drop_constraints :: a -> a

---------------------------------
-- Class of reversible objects --

class Reversible a where
  rev :: a -> a

-----------------------------------
-- Class of parametrized objects --

class Param a where
  free_var :: a -> [Int]
  subs_var :: Int -> Int -> a -> a

