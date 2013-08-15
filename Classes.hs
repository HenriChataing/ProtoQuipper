-- | This module gives the definition of custom Proto-Quipper type
-- classes.  Among these are: 'PPrint', 'Constraint', 'Reversible',
-- 'Param'. These classes were created specifically to be able to
-- overload one or more operations.
module Classes where

import Parsing.Localizing


-- | Definition of a notion of level, corresponding more or less to a
-- depth in a tree. It is used by the PPrint class to indicate to what
-- depth a term / type / pattern is to be printed (it is relevant because of
-- the tree-like structure of those types).
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


-- | The default level, set at 2.
defaultLvl :: Lvl
defaultLvl = Nth 2


-- | This type class includes several pretty printing function, offering some control over the size and
-- form of the display. Four functions are defined, going from the most generic (genprint) down to the
-- default one (pprint), with sprintn and sprint as intermediary.
class PPrint a where
  -- | The most generic function of the PPrint class. 
  genprint :: Lvl                   -- ^ Limit depth.
           -> a                     -- ^ Object to print.
           -> [(Int -> String)]     -- ^ A list of options. Depending on the implementation, this list may vary in size and meaning.
                                    -- For example, consider the term variables, they can be displayed either with their original name, or just the generic name x_n.
                                    -- This is where this argument comes in handy, since it is possible to change this particular point without reprogramming the entire function.
           -> String                -- ^ The result.

  -- | Less generic than genprint. It is still possible to control the size of the display, but the rendering of variables and such is
  -- fixed.
  sprintn :: Lvl -> a -> String

  -- | Application of the function sprintn, with the default level 2.
  sprint  :: a -> String

  -- | Basic printing function. It prints everything, and provides default rendering functions for the variables.
  -- Typically, they will be rendered as /c_n/, where /n/ is the unique id, and /c/ a character that changes depending on the kind of variable (/x/ for term variables, /X/ for type variables, !
  -- for flag variables, /D/ for data constructors).
  pprint :: a -> String



-- | Type class that identifies the objects carrying type constraints of the form (e <: A).
-- The only purpose of this class, except from marking \"constricted\" objects, is to overload the
-- drop_constraints function, used to removed all these annotations.
class Constraint a where
  -- | Removes all the type constraint annotations.
  drop_constraints :: a -> a


-- | Class of objects that implement a reverse function.
class Reversible a where
  -- | Reverse.
  rev :: a -> a


-- | Class of objects parameterized over some integer variable.
-- The limit of this class is that it can only relay one kind of variable, when types for
-- example have two : type variables and flag variables. This is why the types will be given their own
-- class 'Typing.CoreSyntax.KType'.
class Param a where
  -- | Lists all the free variables.
  free_var :: a -> [Int]
  
  -- | Substitutes a free variable by another.
  subs_var :: Int -> Int -> a -> a

