-- | This module provides all the definitions and functions necessary to the manipulation of typing
-- contexts. Typing context are represented as maps from term variables to types. Functions include
-- union, partition, binding of var and patterns

module Typing.TypingContext where

import Utils

import Typing.CoreSyntax
import Typing.TransSyntax

import Monad.QpState
import Monad.QuipperError
import Monad.Namespace
import Monad.Modules

import Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap

-- | Definition of a typing context as a map from term variables to types.
type TypingContext = IntMap Type


-- | Add a binding x |-> t to a typing context. This function also updates the map of global
-- variables that is associated to the current context.
bind_var :: Variable -> Type -> TypingContext -> QpState TypingContext
bind_var x t ctx = do
  -- If the export was requested, update the type of the variable
  update_global_type x t

  -- In any case, adds the binding (x |-> t) in the typing context
  return $ IMap.insert x t ctx


-- | Retrieves a variable's type from the context
-- This function is not suppose to fail, as the scope analysis should have
-- been done during the translation to the interval syntax. If it does, it is because of
-- a programming error.
type_of :: Variable -> TypingContext -> QpState Type
type_of x ctx = do
  case IMap.lookup x ctx of
    Just t ->
        return t
    Nothing -> do
        c <- get_context
        ex <- get_location
        name <- variable_name x
        throwQ $ ProgramError $ "Unbound variable: " ++ name ++ ": at extent " ++ show ex


-- | Given a pattern, create a type matching the pattern, and binds in a new typing context the term variables of the pattern
-- to new type variables created as needed. The construction of the type can generate typing constraints, be they structural flag constraints
-- or constraints coming from the instanciation of some type (eg with data constructors).
bind_pattern :: Pattern -> QpState (Type, TypingContext, ConstraintSet)

-- Unit value
bind_pattern PUnit = do
  -- The flag doesn't need to be a reference, and can have any value
  return (TBang anyflag TUnit, IMap.empty, emptyset)

-- While binding variables, a new type is generated, and bound to x
bind_pattern (PVar x ex) = do
  -- Create a new type, add some information to the flag
  a@(TBang n _) <- new_type
  specify_expression n $ ActualOfP (PVar x ex)
  specify_location n ex

  -- The binding is returned in a singleton map, and no constraints are generated
  return (a, IMap.singleton x a, emptyset)

-- Tuples
bind_pattern (PTuple plist) = do
  -- The flag in front of the tensor type : !p (a1 * .. * an)
  p <- fresh_flag

  -- Bind the patterns of the tuple
  (ptypes, ctx, cset) <- List.foldr (\p rec -> do
                                       (r, ctx, cset) <- rec
                                       (a, ctx', cset') <- bind_pattern p
                                       return (a:r, IMap.union ctx' ctx, cset' <> cset)) (return ([], IMap.empty, emptyset)) plist

  -- Generate the constraints on the flag of the tuple
  pflags <- return $ List.map (\(TBang n _) -> (p, n)) ptypes

  return (TBang p (TTensor ptypes), ctx, pflags <> cset)

-- The datacon already has a type. Instead of creating an entirely new one
-- for the pattern, and stating it must be an instance of the datacon's type,
-- the type of the datacon is used to bind the pattern.
bind_pattern (PDatacon dcon p) = do
  -- Retrieves the type of data constructor 
  dtype <- datacon_def dcon
  
  -- Instanciate the type
  (typ, cset) <- instanciate dtype
  
  -- Check the arguments
  case (typ, p) of
    (TBang _ (TArrow t u), Just p) -> do
        -- The pattern is bound to the type of the argument, and the return type is the return type of the data constructor
        (ctx, cset') <- bind_pattern_to_type p t
        return (u, ctx, cset <> cset')

    (_, Nothing) ->
        -- No binding
        return (typ, IMap.empty, cset)

    _ ->
        fail "In pattern, data constructor takes no argument, when it was given one"

-- While binding to a pattern with a type constraint,
-- do things normally, and add a constraint on the actual type of the pattern
bind_pattern (PConstraint p t) = do
  (typ, ctx, cset) <- bind_pattern p
  (t', cset') <- translate_unbound_type t
  return (typ, ctx, [typ <: t'] <> cset' <> cset)



-- | This function does the same as bind_pattern, expect that it attempts to use the expected
-- type to bind the pattern. This function is typically called while binding a data constructor :
-- the data constructor except its own type, so rather than creating an entirely new one and saying
-- that it must be a subtype of the required one, it is best to bind the pattern directly to this one.
bind_pattern_to_type :: Pattern -> Type -> QpState (TypingContext, ConstraintSet)
bind_pattern_to_type (PVar x ex) t@(TBang n _) = do
  -- Add some information about the variable to the flag
  specify_location n ex
  specify_expression n (ActualOfP $ PVar x ex)

  return (IMap.singleton x t, emptyset)

-- The unit pattern bound to the unit type
bind_pattern_to_type PUnit t@(TBang _ TUnit) = do
  return (IMap.empty, emptyset)

-- Two things have to be done to bind a tuple to a tensor : first
-- make the lengths match, and then bind individually each pattern of the tuple to the
-- corresponding type.
bind_pattern_to_type (PTuple plist) (TBang n (TTensor tlist)) =
  if List.length plist /= List.length tlist then
    fail "Unequal pattern / tuple"

  else do
    ptlist <- return $ List.zip plist tlist
    List.foldl (\rec (p, t) -> do
                  (ctx, cset) <- rec
                  (ctx', cset') <- bind_pattern_to_type p t
                  return (IMap.union ctx' ctx, cset' <> cset)) (return (IMap.empty, emptyset)) ptlist

-- In the case of a datacon constructor, one has to check that the data type it is from is correct (ensured by a subtyping constraint),
-- then bind the (maybe) argument to the type of the data constructor.
bind_pattern_to_type (PDatacon dcon p) typ = do
  -- Retrieves and instanciates the type of the data constructor
  dtype <- datacon_def dcon
  (dtype', cset) <- instanciate dtype
  
  -- Check the argument
  case (dtype', p) of
    (TBang _ (TArrow t u), Just p) -> do
        (ctx, cset') <- bind_pattern_to_type p t
        return (ctx, [u <: typ] <> cset' <> cset)

    (_, Nothing) ->
        return (IMap.empty, [dtype' <: typ] <> cset)

    _ ->
        fail "In pattern, data constructor takes no argument, when it was given one"

-- Same as with the function bind_pattern
bind_pattern_to_type (PConstraint p t) typ = do
  (ctx, cset) <- bind_pattern_to_type p typ
  (t', cset') <- translate_unbound_type t
  return (ctx, [typ <: t'] <> cset <> cset')

-- Any other case is a tying error
bind_pattern_to_type _ _ = do
  fail "Unmatching pattern / type"



-- | Returns the set of the annotation flags of the context.
context_annotation :: TypingContext -> QpState [(Variable, RefFlag)]
context_annotation ctx = do
  return $ IMap.foldWithKey (\x t ann -> case t of
                                           (TBang f _) -> (x, f):ann
                                           (TForall _ _ _ (TBang f _)) -> (x, f):ann) [] ctx


-- | Returns a set of flag constraints forcing the context to be banged.
force_duplicable_context :: TypingContext -> QpState [FlagConstraint]
force_duplicable_context ctx = do
  return $ IMap.fold (\t ann -> case t of
                                  (TBang f _) -> (one, f):ann
                                  (TForall _ _ _ (TBang f _)) -> (one, f):ann) [] ctx


-- | Performs the union of two typing contexts.
merge_contexts :: TypingContext -> TypingContext -> QpState TypingContext
merge_contexts ctx0 ctx1 = do
  return $ IMap.union ctx0 ctx1


-- | Splits the context according to a boolean function. The elements (keys) for which the function returns
-- true are placed on the left, the others on the right.
split_context :: (Variable -> Bool) -> TypingContext -> QpState (TypingContext, TypingContext)
split_context f ctx = do
  return $ IMap.partitionWithKey (\k _ -> f k) ctx


-- | Similar to split_context, with the particular case of a function returning whether
-- an element is or not in a set.
sub_context :: [Variable] -> TypingContext -> QpState (TypingContext, TypingContext)
sub_context set ctx =
  split_context (\x -> List.elem x set) ctx

