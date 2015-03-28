{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

-- | This module provides definitions and functions for manipulating typing contexts. Typing contexts
-- are represented by maps from term variables to types. The functions provided here include union,
-- partition, variable binding, and patterns.

module Typing.TypingContext where

import Utils
import Classes

import Core.Syntax
import Core.Translate
import qualified Core.Environment as Environment
import Core.Namespace

--import Monad.QpState
import Monad.Error

import Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap

-- | A typing context is a map from term variables to type scheme.
type TypingContext = IntMap TypeScheme


-- | Add a binding @/x/ |-> /t/@ to a typing context. This function also updates the map of global
-- variables associated to the current context.
bind_var :: Variable -> TypeScheme -> TypingContext -> QpState TypingContext
bind_var x t ctx = do
  -- In any case, adds the binding (x |-> t) in the typing context
  return $ IMap.insert x t ctx


-- | Retrieve the type of a variable from the context.
-- This function is not supposed to fail, as the scope analysis performed during the translation to
-- the core syntax should have located all the unbound variables. If it does fail, it is because of
-- a programming error.
type_of :: Variable -> TypingContext -> QpState TypeScheme
type_of x ctx = do
  case IMap.lookup x ctx of
    Just t ->
        return t
    Nothing -> do
        ex <- get_location
        name <- variable_name x
        fail $ "Unbound variable: " ++ name ++ ": at extent " ++ show ex


-- | Given a pattern, create a type matching the pattern, and bind, in a new typing context, the term
-- variables of the pattern to new type variables created as needed. The construction of the type can
-- generate typing constraints, be they structural flag constraints or constraints coming from the
-- instantiation of some type (e.g., with data constructors). For example, consider the pattern
-- (/x/, /y/). This function is going to generate the type !^/p/(!^/n/ /a/ * !^/m/ /b/), with the
-- constraints {/p/ <= /n/, /p/ <= /m/} and the bindings [/x/ : !^/n/ /a/, /y/ : !^/m/ /b/].
bind_pattern :: Pattern -> QpState (Type, IntMap Type, ConstraintSet)

-- Wildcard: the wildcard must have a duplicable type, since the value is discarded. No binding is
-- generated.
bind_pattern (PWildcard _) = do
  a <- fresh_type
  return (TypeAnnot 1 $ TypeVar a, IMap.empty, emptyset)

-- Unit pattern.
bind_pattern (PUnit _) = do
  return (TypeAnnot 0 TUnit, IMap.empty, emptyset)

-- Boolean pattern.
bind_pattern (PBool _ b) = do
  return (TypeAnnot 0 TBool, IMap.empty, emptyset)

-- Integer pattern.
bind_pattern (PInt _ n) = do
  return (TypeAnnot 0 TInt, IMap.empty, emptyset)

-- While binding variables, a new type is generated, and bound to x.
bind_pattern (PVar ref x) = do
  -- Create a new type, add some information to the flag
  a <- new_type
  update_ref ref (\ri -> Just ri { rtype = a })
  -- The binding is returned in a singleton map, and no constraints are generated
  return (a, IMap.singleton x a, emptyset)

-- Tuples.
bind_pattern (PTuple _ plist) = do
  -- Bind the patterns of the tuple
  (ptypes, ctx, cset) <- List.foldr (\p rec -> do
      (r, ctx, cset) <- rec
      (a, ctx', cset') <- bind_pattern p
      return (a:r, IMap.union ctx' ctx, cset' <> cset)
    ) (return ([], IMap.empty, emptyset)) plist

  return (TypeAnnot 0 (TTensor ptypes), ctx, cset)

-- Data constructors.
bind_pattern (PDatacon _ dcon p) = do
  -- Retrieves the type of data constructor
  dtype <- datacon_type dcon

  -- Instantiate the type
  (typ, cset) <- instantiate dtype
  a <- new_type

  -- Check the arguments
  case (typ, p) of
    (TypeAnnot _ (TArrow t u), Just p) -> do
        (t', ctx, csett) <- bind_pattern p
        return (a, ctx, [t <: t',a <: u] <> cset <> csett)

    (TypeAnnot n _, Nothing) -> do
        -- No binding
        return (a, IMap.empty, [a <: typ] <> cset)

    _ -> do
        ex <- get_location
        ndcon <- datacon_name dcon
        throwQ (WrongDataArguments ndcon) ex

-- While binding to a pattern with a type constraint,
-- do things normally, and add a constraint on the actual type of the pattern
bind_pattern (PConstraint p (t, typs)) = do
  (typ, ctx, cset) <- bind_pattern p
  t' <- translate_unbound_type t $ Environment.empty { Environment.types = typs }
  return (typ, ctx, [typ <: t'] <> cset)







-- | Return the set of annotation flags of the context.
context_annotation :: TypingContext -> QpState [(Variable, Flag)]
context_annotation ctx = do
  return $ IMap.foldWithKey aux [] ctx
    where
      aux x (TypeScheme _ _ _ (TypeAnnot f _)) ann = (x, f):ann

-- | Return a set of flag constraints forcing the context to be duplicable.
duplicable_context :: TypingContext -> QpState ()
duplicable_context ctx = do
  IMap.foldWithKey aux (return ()) ctx
    where
      aux x (TypeScheme _ _ _ (TypeAnnot f _)) rec = do
        rec
        ref <- variable_reference x
        setFlag f noInfo { c_ref = ref }


instance Context TypingContext where
  ctx0 <+> ctx1 =
    IMap.union ctx0 ctx1

  ctx0 \\ ctx1 =
    ctx0 IMap.\\ ctx1


-- | Split the context according to a boolean function. The elements (keys) for which the function returns
-- 'True' are placed on the left, and the others on the right.
split_context :: (Variable -> Bool) -> TypingContext -> QpState (TypingContext, TypingContext)
split_context f ctx = do
  return $ IMap.partitionWithKey (\k _ -> f k) ctx


-- | Like 'split_context', but for the particular case of a the characteristic function of a set.
sub_context :: [Variable] -> TypingContext -> QpState (TypingContext, TypingContext)
sub_context set ctx =
  split_context (\x -> List.elem x set) ctx


