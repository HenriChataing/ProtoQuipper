-- | This module provides functions that manipulate constraint sets, for the most part to reduce them.
module Typing.Subtyping where

import Classes
import Utils

import Language.Type

import Core.Syntax
import Core.Printer

import Monad.Core as Core
import Monad.Typer
import Monad.Error

import qualified Data.List as List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap


-- | Check whether a given flag constraint is trivial.
nonTrivial :: Flag -> Flag -> Bool
nonTrivial m n =
  (m /= n && n /= 1 && m /= 0)


-- | Using the type specifications registered in the state monad, unfold any subtyping constraints
-- of the form  (user /a/ \<: user /a/'). This functions assumes that the two type names are the same,
-- and that the correct number of arguments has been given.
unfoldTypeConstraint :: [(Type, Variance)] -> [Type] -> [Type] -> ConstraintInfo -> Typer ConstraintSet
unfoldTypeConstraint typargs args args' info = do
  let revinfo = info { actual = not $ actual info } -- For contravariant arguments.
  -- Build the constraints based on the variance of the type arguments.
  let cset = List.foldl (\cset ((_, variance), a, a') ->
        case variance of
          Covariant -> [(a <: a') & info] <> cset
          Contravariant -> [(a' <: a) & revinfo] <> cset
          Equal -> [(a <: a') & info, (a' <: a)  & revinfo] <> cset
          Unrelated -> cset
        ) emptyset $ List.zip3 typargs args args'
  -- Return the complete set.
  return cset


-- | Expand a type synonym.
expandSynonym :: [(Type, Variance)] -> Type -> [Type] -> Type
expandSynonym [] alias [] = alias
expandSynonym ((a, _):args) alias (a':args') =
  case (a, a') of
    (TypeAnnot n (TypeVar a), TypeAnnot n' a') ->
      let alias' = subs a a' $ subs n n' alias in
      expandSynonym args alias' args'
    _ -> throwNE $ ProgramError "Subtyping:expandSynonym: inadequate type arguments in type alias"
expandSynonym [] _ _ = throwNE $ ProgramError "Subtyping:expandSynonym: too many type arguments"
expandSynonym _ _ [] = throwNE $ ProgramError "Subtyping:expandSynonym: missing type arguments"


-- | Try expanding a type synonym: if the type argument is indeed a type synonym, the function will
-- expand the definition and return true. Else, the result will be false.
tryExpandSynonym :: ConstantType -> [Type] -> Typer (LinearType, Bool)
tryExpandSynonym (TypeBuiltin s) args = return (TypeApply (TypeBuiltin s) args, False)
tryExpandSynonym (TypeUser typ) args = do
  typedef <- runCore $ getTypeDefinition typ
  case typedef of
    Synonym typargs _ alias -> do
      let TypeAnnot _ exptyp = expandSynonym typargs alias args
      return (exptyp, True)
    Algebraic _ _ _ -> return (TypeApply (TypeUser typ) args, False)


-- | Reduce a single type constraint from a constraint set, and return the smaller constraints
-- resulting from the breakdown. The function is recursive, and the constraint set returned
-- should only contain atomic and semi-atomic constraints.
breakConstraint :: TypeConstraint -> Typer ConstraintSet
-- For type constraints with constructors: clearly identify each constructor before deciding what
-- to do with the flags. In particular, if the type is a qubit, we must unset the flags associated
-- with each type.
breakConstraint (Subtype t @ (TypeAnnot n (TypeApply c args)) u @ (TypeAnnot m (TypeApply c' args')) info) = do
  -- In the unlikely event that the constructor are already identical, immediatly deal with the
  -- constraint with expanding synonyms.
  if c == c' && List.length args == List.length args' then do
    -- Update the constraint information if needed.
    let info' = case sourceType info of
          Just a -> info
          Nothing -> info { sourceType = Just $ if actual info then t else u }
    case (c, args, args') of
      -- Deal with builtins directly.
      (TypeBuiltin "qubit", [], []) -> do
        unsetFlag n info'
        unsetFlag m info'
        return emptyset
      (TypeBuiltin "int", [], []) -> return emptyset
      (TypeBuiltin "bool", [], []) -> return emptyset
      (TypeBuiltin "unit", [], []) -> return emptyset
      (TypeBuiltin "circ", [t, u], [t', u']) -> do
        cset <- breakConstraint (Subtype t t' info')
        cset' <- breakConstraint (Subtype u u' info')
        return $ cset <> cset'
      (TypeBuiltin "->", [t, u], [t', u']) -> do
        cset <- breakConstraint (Subtype t' t info' { actual = not $ actual info'}) -- Contravariant.
        cset' <- breakConstraint (Subtype u u' info') -- Covariant.
        return $ (Le m n info') <> cset <> cset'
      (TypeBuiltin "*", _, _) ->
        List.foldl (\rec (t, t') -> do
            cset <- rec
            cset' <- breakConstraint (Subtype t t' info') -- Covariant.
            return $ cset <> cset'
          ) (return $ (Le m n info') <> emptyset) $ List.zip args args'
      (TypeBuiltin s, _, _) ->
        throwNE $ ProgramError $ "Subtyping:breakConstraint: undefined builtin type " ++ s
      -- For type constructors (algebraic or alias), we must fetch the definition.
      (TypeUser c, args, args') -> do
        typedef <- runCore $ getTypeDefinition c
        cset <- unfoldTypeConstraint (arguments typedef) args args' info'
        return $ (Le m n info') <> cset

  -- If the type arguments are not equal, try expanding type synonyms until the type are equals, or
  -- the types cannot be expanded anymore.
  else do
    (t', expt) <- tryExpandSynonym c args
    (u', expu) <- tryExpandSynonym c' args'
    -- One of the two was indeed a synonym: make a recursive call with the produced types.
    if expt || expu then breakConstraint $ Subtype (TypeAnnot n t') (TypeAnnot m u') info
    -- Both were NOT synonyms: this is a typing error.
    else throwTypingError t u info

-- In the two following cases, we must still check the type constructor: if it corresponds to a qubit,
-- we must unset the flags attached to each type.
breakConstraint (Subtype t @ (TypeAnnot n (TypeVar x)) u @ (TypeAnnot m (TypeApply c args)) info) = do
  let info' = case sourceType info of
        Just a -> info
        Nothing -> info { sourceType = Just u }
  case c of
    TypeBuiltin "qubit" -> do
      unsetFlag n info'
      unsetFlag m info'
    _ -> return ()
  let constraint = SubLinearType (TypeVar x) (TypeApply c args) info'
  return $ ConstraintSet [constraint] []

breakConstraint (Subtype t @ (TypeAnnot n (TypeApply c args)) u @ (TypeAnnot m (TypeVar x)) info) = do
  let info' = case sourceType info of
        Just a -> info
        Nothing -> info { sourceType = Just t }
  case c of
    TypeBuiltin "qubit" -> do
      unsetFlag n info'
      unsetFlag m info'
    _ -> return ()
  let constraint = SubLinearType (TypeApply c args) (TypeVar x) info'
  return $ ConstraintSet [constraint] []

-- Hidden atomic constraint.
breakConstraint (Subtype (TypeAnnot n (TypeVar x)) (TypeAnnot m (TypeVar y)) info) = do
  let constraint = SubLinearType (TypeVar x) (TypeVar y) info
  return $ ConstraintSet [constraint] [Le m n info]

-- Linear constraints. Note: we shouldn't have to break linear constraints on type applications, so
-- we will ignore these cases and suppose only atomic and semi-atomic constraints remain, which will
-- allow us to return immediatly with a singleton set.
breakConstraint c @ (SubLinearType _ _ _) =
  return $ ConstraintSet [c] []
