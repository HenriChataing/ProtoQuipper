-- | This module provides definitions and functions for manipulating
-- typing contexts. Typing contexts are represented by maps from term
-- variables to types. The functions provided here include union,
-- partition, variable binding, and patterns.

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

-- | A typing context is a map from term variables to types.
type TypingContext = IntMap Type


-- | Add a binding @/x/ |-> /t/@ to a typing context. This function also updates the map of global
-- variables associated to the current context.
bind_var :: Variable -> Type -> TypingContext -> QpState TypingContext
bind_var x t ctx = do
  -- In any case, adds the binding (x |-> t) in the typing context
  return $ IMap.insert x t ctx


-- | Retrieve the type of a variable from the context.
-- This function is not supposed to fail, as the scope analysis performed during the translation to the
-- core syntax should have located all the unbound variables. If it does fail, it is because of
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


-- | Given a pattern, create a type matching the pattern, and bind, in a new typing context, the term variables of the pattern
-- to new type variables created as needed. The construction of the type can generate typing constraints, be they structural flag constraints
-- or constraints coming from the instantiation of some type (e.g., with data constructors).
-- For example, consider the pattern (/x/, /y/). This function is going to generate the type !^/p/(!^/n/ /a/ * !^/m/ /b/), with the constraints {/p/ <= /n/, /p/ <= /m/}
-- and the bindings [/x/ : !^/n/ /a/, /y/ : !^/m/ /b/].
bind_pattern :: Pattern -> QpState (Type, TypingContext, ConstraintSet)

-- Wildcard: the wildcard must have a duplicable type, since
-- the value is discarded. No binding is generated.
bind_pattern PWildcard = do
  a <- fresh_type
  return (TBang 1 $ TVar a, IMap.empty, emptyset)

-- Unit pattern
bind_pattern PUnit = do
  return (TBang 0 TUnit, IMap.empty, emptyset)

-- Boolean pattern
bind_pattern (PBool b) = do
  return (TBang 0 TBool, IMap.empty, emptyset)
  
-- Integer pattern
bind_pattern (PInt n) = do
  return (TBang 0 TInt, IMap.empty, emptyset)
  
-- While binding variables, a new type is generated, and bound to x
bind_pattern (PVar x) = do
  -- Create a new type, add some information to the flag
  a <- new_type
  -- The binding is returned in a singleton map, and no constraints are generated
  return (a, IMap.singleton x a, emptyset)

-- Tuples
bind_pattern (PTuple plist) = do
  -- Bind the patterns of the tuple
  (ptypes, ctx) <- List.foldr (\p rec -> do
                                 (r, ctx) <- rec
                                 (a, ctx', _) <- bind_pattern p
                                 return (a:r, IMap.union ctx' ctx)) (return ([], IMap.empty)) plist

  return (TBang 0 (TTensor ptypes), ctx, emptyset)

-- Data constructors
bind_pattern (PDatacon dcon p) = do
  -- Retrieves the type of data constructor 
  dtype <- datacon_def dcon
  
  -- Instantiate the type
  (typ, cset) <- instantiate dtype

  -- Check the arguments
  case (typ, p) of
    (TBang _ (TArrow t u@(TBang n _)), Just p) -> do
        (t', ctx, csett) <- bind_pattern p
        return (u, ctx, [t' <: t] <> cset <> csett)

    (TBang n _, Nothing) -> do
        -- No binding
        return (typ, IMap.empty, cset)

    _ -> do
        ex <- get_location
        ndcon <- datacon_name dcon
        throwQ $ LocatedError (WrongDataArguments ndcon) ex

-- While binding to a pattern with a type constraint,
-- do things normally, and add a constraint on the actual type of the pattern
bind_pattern (PConstraint p (t, typs)) = do
  (typ, ctx, cset) <- bind_pattern p
  t' <- translate_unbound_type t $ empty_label { l_types = typs }
  return (typ, ctx, [typ <: t'] <> cset)

-- Relay the location
bind_pattern (PLocated p ex) = do
  set_location ex
  bind_pattern p




-- | Like 'bind_pattern', but use the provided type as the type of the pattern.
-- This function is typically called while binding a data constructor:
-- the data constructor contains its own type, so rather than creating an entirely new one and saying
-- that it must be a subtype of the required one, it is best to bind the pattern directly to this.
bind_pattern_to_type :: Pattern -> Type -> QpState (TypingContext, ConstraintSet)
-- The wildcard can be bound to any type, as long as it is duplicable.
bind_pattern_to_type PWildcard a@(TBang n _) = do
  -- Set the flag to one, and return
  set_flag n no_info
  return (IMap.empty, emptyset)

bind_pattern_to_type (PVar x) t@(TBang n _) = do
  return (IMap.singleton x t, emptyset)

-- The unit pattern bound to the unit type
bind_pattern_to_type PUnit t@(TBang _ TUnit) = do
  return (IMap.empty, emptyset)

-- A boolean pattern bound to the boolean type
bind_pattern_to_type (PBool b) t@(TBang _ TBool) = do
  return (IMap.empty, emptyset)

-- The unit pattern bound to the unit type
bind_pattern_to_type (PInt n) t@(TBang _ TInt) = do
  return (IMap.empty, emptyset)

-- Two things have to be done to bind a tuple to a tensor: first
-- make the lengths match, and then bind individually each pattern of the tuple to the
-- corresponding type.
bind_pattern_to_type (PTuple plist) (TBang n (TTensor tlist)) =
  if List.length plist /= List.length tlist then do
    -- Typing error

    -- Location
    ex <- get_location
    
    -- Build and actual type: a1 * .. * an
    act <- List.foldr (\_ rec -> do
                         r <- rec
                         a <- new_type
                         return $ a:r) (return []) plist
    act <- pprint_lintype_noref $ TTensor act    
    nact <- pprint_lintype_noref $ TTensor tlist

    expr <- pprint_pattern_noref $ PTuple plist

    throwQ $ LocatedError (DetailedTypingError act nact Nothing expr) ex
 

  else do
    ptlist <- return $ List.zip plist tlist
    List.foldl (\rec (p, t) -> do
                  (ctx, cset) <- rec
                  (ctx', cset') <- bind_pattern_to_type p t
                  return (IMap.union ctx' ctx, cset' <> cset)) (return (IMap.empty, emptyset)) ptlist

-- In the case of a datacon constructor, one has to check that the data type it is from is correct (ensured by a subtyping constraint),
-- then bind the (maybe) argument to the type of the data constructor.
bind_pattern_to_type (PDatacon dcon p) typ = do
  -- Retrieves and instantiates the type of the data constructor
  dtype <- datacon_def dcon
  (dtype', cset) <- instantiate dtype
  
  -- Check the argument
  case (dtype', p) of
    (TBang _ (TArrow t u), Just p) -> do
        (ctx, cset') <- bind_pattern_to_type p t
        return (ctx, [u <: typ] <> cset' <> cset)

    (_, Nothing) ->
        return (IMap.empty, [dtype' <: typ] <> cset)

    _ -> do
        ex <- get_location
        ndcon <- datacon_name dcon
        throwQ $ LocatedError (WrongDataArguments ndcon) ex

-- Same as with the function bind_pattern
bind_pattern_to_type (PConstraint p (t, typs)) typ = do
  (ctx, cset) <- bind_pattern_to_type p typ
  t' <- translate_unbound_type t $ empty_label { l_types = typs }
  return (ctx, [typ <: t'] <> cset)

-- With location
bind_pattern_to_type (PLocated p ex) t = do
  set_location ex
  bind_pattern_to_type p t

-- Any other case is a tying error
bind_pattern_to_type p t = do
  -- Location
  ex <- get_location

  -- Build the actual type of p
  (a, _, _) <- bind_pattern p
  act <- pprint_type_noref a
  nact <- pprint_type_noref t

  expr <- pprint_pattern_noref p

  throwQ $ LocatedError (DetailedTypingError act nact Nothing expr) ex



-- | Return the set of annotation flags of the context.
context_annotation :: TypingContext -> QpState [(Variable, RefFlag)]
context_annotation ctx = do
  return $ IMap.foldWithKey (\x t ann -> case t of
                                           (TBang f _) -> (x, f):ann
                                           (TForall _ _ _ (TBang f _)) -> (x, f):ann) [] ctx


-- | Return a set of flag constraints forcing the context to be duplicable.
duplicable_context :: TypingContext -> QpState ()
duplicable_context ctx = do
  IMap.foldWithKey (\x t rec -> do
                      rec
                      ex <- variable_location x
                      case t of
                        TBang f _ -> set_flag f no_info { expression = EVar x, loc = ex } 
                        TForall _ _ _ (TBang f _) -> set_flag f no_info { expression = EVar x, loc = ex }) (return ()) ctx


-- | Perform the union of two typing contexts. The \<+\> operator respects the order of the arguments
-- when calling 'IMap.union' (meaning it is left-biased).
(<+>) :: TypingContext -> TypingContext -> TypingContext
ctx0 <+> ctx1 =
  IMap.union ctx0 ctx1


-- | Split the context according to a boolean function. The elements (keys) for which the function returns
-- 'True' are placed on the left, and the others on the right.
split_context :: (Variable -> Bool) -> TypingContext -> QpState (TypingContext, TypingContext)
split_context f ctx = do
  return $ IMap.partitionWithKey (\k _ -> f k) ctx


-- | Like 'split_context', but for the particular case of a the characteristic function of a set.
sub_context :: [Variable] -> TypingContext -> QpState (TypingContext, TypingContext)
sub_context set ctx =
  split_context (\x -> List.elem x set) ctx

