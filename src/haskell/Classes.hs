{-# LANGUAGE MultiParamTypeClasses #-}

-- | This module gives the definition of custom Proto-Quipper type classes.  Among these are:
-- 'PPrint', 'Constraint', 'Reversible', 'Param'. These classes were created specifically to be
-- able to overload one or more operations.
module Classes where

import Utils
import Parsing.Location

import Data.IntSet (IntSet)

-- | This type class includes several pretty printing functions, offering some control over the
-- size and form of the display. Four functions are defined, going from the most generic ('genprint')
-- down to the default one ('pprint'), with 'sprintn' and 'sprint' as intermediaries. At least
-- 'genprint' and 'sprintn' must be defined in an instance.
class PPrint a where
  -- | The most generic function of the 'PPrint' class.
  genprint :: Lvl           -- ^ The depth limit.
    -> [(Int -> String)]    -- ^ A list of options. Depending on the implementation, this list may
                            -- vary in size and meaning. For example, consider term variables; they
                            -- can be displayed either with their original name, or just the generic
                            -- name /x_n/. This is where this argument comes in handy, since it is
                            -- possible to change this particular point without re-programming the
                            -- entire function.
    -> a                    -- ^ The object to print.
    -> String               -- ^ The result.

  -- | Less generic than 'genprint'. It is still possible to control the size of the output, but the
  -- rendering of variables and such is fixed.
  sprintn :: Lvl -> a -> String

  -- | Same as 'sprintn', but with the default level 2.
  sprint  :: a -> String

  -- | Basic printing function. It prints everything, and provides default rendering functions for
  -- the variables. Typically, they will be rendered as /c_n/, where /n/ is the unique id, and /c/
  -- a character that changes depending on the kind of variable (/x/ for term variables, /X/ for type
  -- variables, ! for flag variables, /D/ for data constructors, /A/ for algebraic or synonym types).
  pprint :: a -> String

  -- By default, pprint is a call to sprintn with n = Inf.
  pprint a = sprintn Inf a
  -- By default, sprintn is a call to sprintn with n = default_lvl.
  sprint a = sprintn default_lvl a



-- | This type class identifies the objects carrying type constraints of the form (/e/ <: /A/).
-- The only purpose of this class, except from marking \"constrained\" objects, is to overload the
-- 'uncoerce' function, used to remove all these annotations.
class Coerced a where
  -- | Removes all type constraint annotations.
  uncoerce :: a -> a


-- | A type class for objects parameterized over some integer variables.
-- A limitation of this class is that it can only handle one kind of variable, whereas types, for
-- example, have two: type variables and flag variables. This is why the set of types will be given
-- its own class 'Typer.CoreSyntax.KType'.
class TermObject a where
  -- | List all the free variables.
  freevar :: a -> IntSet


-- | The class of objects whose type is \'kind\'. Instances include, of course, 'LinearType' and
-- 'Type', but also everything else that contains types: 'TypeConstraint', 'ConstraintSet',
-- ['TypeConstraint'], etc. The only purpose of this class is to overload the functions listed below.
class TypeObject a where
  -- | Return the list of flag references.
  freeflag :: a -> IntSet
  -- | Return @True@ iff the argument is of the form \A -> B\.
  isFunction :: a -> Bool
  -- | Return @True@ iff the argument is a quantum data type.
  isQuantum :: a -> Bool


-- | A type class of objects where variables can be substituted.
class Subs a b where
  -- | Substitute a variable.
  subs :: Int -> b -> a -> a


-- | The class of contexts. For example: typing context, labelling context, evaluation context.
class Context a where
  -- | The union of two contexts.
  (<+>) :: a -> a -> a
  -- | the difference between two contexts.
  (\\) :: a -> a -> a
