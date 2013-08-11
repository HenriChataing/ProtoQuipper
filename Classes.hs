-- | This module gives the definition of custom Proto-Quipper type classes.
-- Amongst these are: PPrint, Constraint, Reversible, Param.
module Classes where

import Parsing.Localizing


-- | Recursion level (depth of tree). Used to limit the display
-- of terms, types and patterns to a certain depth in the syntax tree.
data Lvl =
    Nth Int      -- ^ Depth n.
  | Inf          -- ^ Infinite depth (print everything).


-- | Increases the recursion level.
incr :: Lvl -> Lvl
incr (Nth n) = Nth (n+1)
incr Inf = Inf


-- | Decreases the recursion level.
decr :: Lvl -> Lvl
decr (Nth n) = Nth (n-1)
decr Inf = Inf


-- | Default level, set at 2.
defaultLvl :: Lvl
defaultLvl = Nth 2


-- | Objects implementing  several pretty printing functions.
class PPrint a where
  -- | Printing with options : the options are printing functions specific to variables. For example
  -- the variable of id n can either be represented as x_n, or by its actual name.
  genprint :: Lvl -> a -> [(Int -> String)] -> String

  -- | Print until Lvl = n.
  sprintn :: Lvl -> a -> String

  -- | Print until the default level.
  sprint  :: a -> String

  -- | Print everything.
  pprint :: a -> String



-- | Objects that can include type constraints, typically patterns and expressions.
class Constraint a where
  -- | Remove all the type constraint annotations.
  drop_constraints :: a -> a


-- | Objects that implement a reverse function.
class Reversible a where
  -- | Reverse.
  rev :: a -> a


-- | Objects parametrized over some integer variable.
class Param a where
  -- | List all the free variables.
  free_var :: a -> [Int]
  
  -- | Replace a free variable by another one.
  subs_var :: Int -> Int -> a -> a

