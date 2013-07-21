-- | This module provides all the definitions and functions necessary to the manipulation of typing
-- contexts. Typing context are represented as maps from term variables to types. Functions include
-- union, partition, binding of var and patterns

module TypingContext where

import CoreSyntax

import QpState
import QuipperError
import Utils

import Namespace
import Modules

import Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap

-- | Definition of a typing context as a map from term variables to types
type TypingContext = IntMap Type


-- | Add a binding to the context, from the variable x to the type t
bind_var :: Variable -> Type -> TypingContext -> QpState TypingContext
bind_var x t ctx = do
  -- If the export was requested, update the type of the variable
  stt <- get_context
  cm <- get_module
  set_context $ stt { cmodule = cm { global_types = IMap.update (\_ -> Just t) x $ global_types cm } }

  return $ IMap.insert x t ctx


-- | Retrieves a variable's type from the context
-- This function is not suppose to fail, as the scope analysis should have
-- been done during the translation to the interval syntax. If it does, it's
-- a programming error
type_of :: Variable -> TypingContext -> QpState Type
type_of x ctx = do
  case IMap.lookup x ctx of
    Just t ->
        return t
    Nothing -> do
        c <- get_context
        ex <- get_location
        case IMap.lookup x $ varcons $ namespace c of
          Just name -> throwQ $ ProgramError $ "Unbound variable: " ++ name ++ ": at extent " ++ show ex
          Nothing -> throwQ $ ProgramError $ "Unbound variable: " ++ subvar 'x' x ++ ": at extent " ++ show ex


-- | Given a pattern, create a type matching the pattern, and binds the term variables of the pattern
-- to new type variables, created as needed
bind_pattern :: Pattern -> TypingContext -> QpState (Type, TypingContext, ConstraintSet)
bind_pattern (PLocated p ex) ctx = do
  set_location ex
  bind_pattern p ctx

-- Unit value
bind_pattern PUnit ctx = do
  -- Detailed information
  ex <- get_location
  n <- fresh_flag_with_value Any
  specify_expression n $ ActualOfP PUnit
  specify_location n ex

  return (TBang n TUnit, ctx, emptyset)

-- While binding variables, a new type is generated, and bound to x
bind_pattern (PVar x) ctx = do
  -- Detailed information 
  ex <- get_location
  n <- fresh_flag
  specify_expression n $ ActualOfP (PVar x)
  specify_location n ex

  a <- fresh_type

  ctx' <- bind_var x (TBang n (TVar a)) ctx
  return (TBang n (TVar a), ctx', emptyset)

-- Tuples
bind_pattern (PTuple plist) ctx = do
  -- Detailed information
  ex <- get_location
  n <- fresh_flag
  specify_expression n $ ActualOfP (PTuple plist)
  specify_location n ex

  -- Bind the patterns of the tuple
  (ptypes, ctx, cset) <- List.foldr (\p rec -> do
                                 (r, ctx, cset) <- rec
                                 (p', ctx, cset') <- bind_pattern p ctx
                                 return ((p':r), ctx, cset <> cset')) (return ([], ctx, emptyset)) plist

  -- Generate the constraints on the flag of the tuple
  pflags <- return $ List.foldl (\fgs (TBang f _) -> (n, f):fgs) [] ptypes

  return (TBang n (TTensor ptypes), ctx, cset <> ([], pflags))

-- While binding datacons, a new type is generated for the inner one,
-- with the condition that it is a subtype of the type required by the data constructor
bind_pattern (PDatacon dcon p) ctx = do
  -- Definition of the data constructor 
  dtype <- datacon_def dcon
  
  -- Instanciate the type
  (typ, cset) <- instanciate dtype
  
  -- Check the arguments
  case (typ, p) of
    (TBang _ (TArrow t u), Just p) -> do
        -- The pattern is bound to the type of the argument, and the return type is the return type of the data constructor
        (ctx', cset') <- bind_pattern_to_type p t ctx
        return (u, ctx', cset <> cset')

    (_, Nothing) ->
        return (typ, ctx, cset)

    _ ->
        fail "In pattern, data constructor takes no argument, when it was given one"


-- | This function does the same as bind_pattern, expect that it attempts to use the expected
-- type to bind the pattern. This function is typically called while binding a data constructor :
-- the data constructor except its own type, so rather than creating an entirely new one and saying
-- that it must be a subtype of the required one, it is best to bind the pattern directly to this one
bind_pattern_to_type :: Pattern -> Type -> TypingContext -> QpState (TypingContext, ConstraintSet)
bind_pattern_to_type (PLocated p ex) t ctx = do
  set_location ex
  bind_pattern_to_type p t ctx

bind_pattern_to_type (PVar x) t ctx = do
  ctx' <- bind_var x t ctx
  return (ctx', emptyset)

bind_pattern_to_type PUnit t@(TBang _ TUnit) ctx = do
  return (ctx, emptyset)

bind_pattern_to_type (PTuple plist) (TBang n (TTensor tlist)) ctx =
  let bind_list = (\plist tlist ctx ->
                     case (plist, tlist) of 
                       ([], []) ->
                           return (ctx, ([], []))

                       (p:prest, t:trest) -> do
                           (ctx', cset) <- bind_pattern_to_type p t ctx
                           (ctx'', cset') <- bind_list prest trest ctx'
                           return (ctx'', cset <> cset')

                       -- In case the list are of unequal size
                       _ ->
                           fail "Unequal tuple / tensor")
  in do
    -- Apply the binding function to the list
    (ctx', constraints) <- bind_list plist tlist ctx
    return (ctx', constraints)

bind_pattern_to_type (PDatacon dcon p) typ ctx = do
  dtype <- datacon_def dcon
  (dtype', cset) <- instanciate dtype
  
  case (dtype', p) of
    (TBang _ (TArrow t u), Just p) -> do
        -- The pattern is bound to the type of the argument, and the return type is the return type of the data constructor
        (ctx', cset') <- bind_pattern_to_type p t ctx
        return (ctx', [u <: typ] <> cset <> cset')

    (_, Nothing) ->
        return (ctx, [dtype' <: typ] <> cset)

    _ ->
        fail "In pattern, data constructor takes no argument, when it was given one"

bind_pattern_to_type _ _ _ = do
  fail "Unmatching pattern / type"



-- | Return the set of the annotation flags of the context
context_annotation :: TypingContext -> QpState [(Variable, RefFlag)]
context_annotation ctx = do
  return $ IMap.foldWithKey (\x (TBang f _) ann -> (x, f):ann) [] ctx


-- | Return a set of flag constraints forcing the context to be banged
have_duplicable_context :: TypingContext -> QpState [FlagConstraint]
have_duplicable_context ctx = do
  return $ IMap.fold (\(TBang f _) ann -> (one, f):ann) [] ctx


-- | Perform the union of two typing contexts
merge_contexts :: TypingContext -> TypingContext -> QpState TypingContext
merge_contexts ctx0 ctx1 = do
  return $ IMap.union ctx0 ctx1


-- | Split the context according to a boolean function. The elements (keys) for which the function returns
-- true are placed on the left, the others on the right
split_context :: (Variable -> Bool) -> TypingContext -> QpState (TypingContext, TypingContext)
split_context f ctx = do
  return $ IMap.partitionWithKey (\k _ -> f k) ctx


-- | Similar to split_context, with the particular case of a function returning whether
-- an element is or not in a set.
sub_context :: [Variable] -> TypingContext -> QpState (TypingContext, TypingContext)
sub_context set ctx =
  split_context (\x -> List.elem x set) ctx

