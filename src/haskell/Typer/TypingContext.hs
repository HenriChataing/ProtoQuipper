{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

-- | This module provides definitions and functions for manipulating typing contexts. Typing contexts
-- are represented by maps from term variables to types. The functions provided here include union,
-- partition, variable binding, and patterns.

module Typer.TypingContext where

import Utils
import Classes
import Parsing.Location hiding (location)

import qualified Language.Constructor as Constructor (typ, name)

import Core.Syntax
import Core.Translate
import qualified Core.Environment as Environment

import Monad.Error
import Monad.Typer as Typer
import Monad.Core as Core hiding (environment)

import Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet as IntSet (IntSet, member)

import Control.Monad.Trans.State
import Control.Monad.Trans


-- | A typing context is a map from term variables to type scheme.
type TypingContext = IntMap TypeScheme

instance Context TypingContext where
  ctx0 <+> ctx1 = IntMap.union ctx0 ctx1
  ctx0 \\ ctx1 = ctx0 IntMap.\\ ctx1


-- | Add a binding @/x/ |-> /t/@ to a typing context. This function also updates the map of global
-- variables associated to the current context.
bindVar :: Variable -> TypeScheme -> TypingContext -> Typer TypingContext
bindVar x t ctx = do
  -- In any case, adds the binding (x |-> t) in the typing context.
  return $ IntMap.insert x t ctx


-- | Retrieve the type of a variable from the context.
-- This function is not supposed to fail, as the scope analysis performed during the translation to
-- the core syntax should have located all the unbound variables. If it does fail, it is because of
-- a programming error. If the type of the variable is not found, the function checks the global
-- typemap in the Typer Monad.
typeOf :: Variable -> TypingContext -> Typer TypeScheme
typeOf x ctx = do
  case IntMap.lookup x ctx of
    Just t -> return t
    Nothing -> do
      typemap <- gets Typer.typemap
      case IntMap.lookup x typemap of
        Just t -> return t
        Nothing -> do
          name <- runCore $ variableName x
          fail $ "TypingContext.typeOf:Unbound variable " ++ name


-- | Given a pattern, create a type matching the pattern, and bind, in a new typing context, the term
-- variables of the pattern to new type variables created as needed. The construction of the type can
-- generate typing constraints, be they structural flag constraints or constraints coming from the
-- instantiation of some type (e.g., with data constructors). For example, consider the pattern
-- (/x/, /y/). This function is going to generate the type !^/p/(!^/n/ /a/ * !^/m/ /b/), with the
-- constraints {/p/ <= /n/, /p/ <= /m/} and the bindings [/x/ : !^/n/ /a/, /y/ : !^/m/ /b/].
bindPattern :: Pattern -> Typer (Pattern, Type, IntMap Type, ConstraintSet)
-- Wildcard: the wildcard must have a duplicable type, since the value is discarded. No binding is
-- generated.
bindPattern (PWildcard info) = do
  a <- runCore Core.freshType
  let typ = TypeAnnot 1 $ TypeVar a
  return (PWildcard info { typ = typ } , typ, IntMap.empty, emptyset)
-- Constant patterns.
bindPattern (PConstant info c) = do
  let typ = case c of
        ConstInt _ -> apply 0 "int" []
        ConstBool _ -> apply 0 "bool" []
        ConstUnit -> apply 0 "unit" []
  return (PConstant info { typ = typ } c, typ, IntMap.empty, emptyset)
-- While binding variables, a new type is generated, and bound to x.
bindPattern (PVar info x) = do
  a <- runCore newType
  return (PVar info { typ = a } x, a, IntMap.singleton x a, emptyset)

-- Tuples.
bindPattern (PTuple info tuple) = do
  -- Bind the patterns of the tuple.
  (tuple, typs, ctx, cset) <- List.foldr (\p rec -> do
      (tuple, typs, ctx, cset) <- rec
      (p', a, ctx', cset') <- bindPattern p
      return (p':tuple, a:typs, IntMap.union ctx' ctx, cset' <> cset)
    ) (return ([], [], IntMap.empty, emptyset)) tuple
  -- Build the tensor type.
  let typ = apply 0 "*" typs
  return (PTuple info { typ = typ } tuple, typ, ctx, cset)

-- Data constructors.
bindPattern (PDatacon info cons p) = do
  -- Retrieves the type of data constructor, and instantiate it.
  def <- runCore $ getConstructorInfo cons
  (typ, cset) <- instantiate $ Constructor.typ def
  a <- runCore newType
  -- Check the arguments.
  case (typ, p) of
    (TypeAnnot _ (TypeApply (TypeBuiltin "->") [t, u]), Just p) -> do
      (p', t', ctx, csett) <- bindPattern p
      return (
          PDatacon info { typ = a } cons $ Just p', a, ctx,
          [t <: t', a <: u] <> cset <> csett)

    (_, Nothing) -> do
      return (PDatacon info { typ = a } cons Nothing, a, IntMap.empty, [a <: typ] <> cset)

    _ -> throwNE (WrongDataArguments $ Constructor.name def) $ extent info

-- While binding to a pattern with a type constraint, do things normally, and add a constraint on
-- the actual type of the pattern. The constraint is removed in the returned pattern.
bindPattern (PCoerce p t typs) = do
  (p', typ, ctx, cset) <- bindPattern p
  let state = TranslateState {
        bound = False,
        location = unknownExtent,
        environment = Environment.empty,
        types = typs,
        currentModule = ""
      }
  (t', _) <- runCore $ runStateT (translateUnboundType t) state
  return (p', typ, ctx, [typ <: t'] <> cset)


-- | Return the set of annotation flags of the context.
contextAnnotation :: TypingContext -> [(Variable, Flag)]
contextAnnotation ctx = do
  IntMap.foldWithKey (\x (TypeScheme _ _ _ (TypeAnnot f _)) ann -> (x, f):ann) [] ctx


-- | Return a set of flag constraints forcing the context to be duplicable.
duplicableContext :: TypingContext -> Typer ()
duplicableContext ctx = do
  IntMap.foldWithKey (\x (TypeScheme _ _ _ (TypeAnnot f _)) rec -> do
        rec
        setFlag f noInfo
      ) (return ()) ctx


-- | Split the context according to a boolean function. The elements (keys) for which the function returns
-- 'True' are placed on the left, and the others on the right.
splitContext :: (Variable -> Bool) -> TypingContext -> Typer (TypingContext, TypingContext)
splitContext f ctx = do
  return $ IntMap.partitionWithKey (\k _ -> f k) ctx


-- | Like 'splitContext', but for the particular case of a the characteristic function of a set.
subContext :: IntSet -> TypingContext -> Typer (TypingContext, TypingContext)
subContext set ctx =
  splitContext (\x -> IntSet.member x set) ctx
