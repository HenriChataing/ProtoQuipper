module TypingContext where

import CoreSyntax

import Contexts

import Data.Map as Map
import Data.List as List

{-
   Haskell representation of a typing context, as a map of bindings variable <-> type
-}

type TypingContext = Map.Map Variable Type

{-
  Manipulation of the bindings (typing context) :
  
  - bind_var : add a new binding x <-> t in the context
  - bind_pattern : add as many bindings as the free variables of the pattern in the current context

  - type_of : returns the type assiociated with a variable (fails if the variable is not present in the context)

  And more global functions, applying to the whole context :
  - context_annotation : returns the vector of the flag annotations of the types in the context
  - merge_contexts : merge two typing contexts, nothing is done to check duplicate variables
  - split_context : split the context accordingly to a boolean function
-}

bind_var :: Variable -> Type -> TypingContext -> State TypingContext
bind_pattern :: Pattern -> Type -> TypingContext -> State TypingContext
type_of :: Variable -> TypingContext -> State Type

context_annotation :: TypingContext -> State [(Variable, Flag)]
merge_contexts :: TypingContext -> TypingContext -> State TypingContext
split_context :: (Variable -> Bool) -> TypingContext -> State (TypingContext, TypingContext)
sub_context :: [Variable] -> TypingContext -> State (TypingContext, TypingContext)
----------------------------------------------------------------------------------
bind_var x t ctx = do
  return $ Map.insert x t ctx

bind_pattern p (TExp f (TDetailed t _)) ctx = do
  bind_pattern p (TExp f t) ctx

bind_pattern PUnit (TExp _ TUnit) ctx = do
  return ctx

bind_pattern (PVar x) t ctx = do
  bind_var x t ctx

bind_pattern (PPair p q) (TExp _ (TTensor t u)) ctx = do
  ctx' <- bind_pattern p t ctx
  bind_pattern q u ctx'


type_of x ctx = do
  case Map.lookup x ctx of
    Just t -> return t
    Nothing -> fail "Unbound variable"


context_annotation ctx = do
  return $ Map.foldWithKey (\x (TExp f _) ann -> (x, f):ann) [] ctx

merge_contexts ctx0 ctx1 = do
  return $ Map.union ctx0 ctx1

split_context f ctx = do
  return $ Map.partitionWithKey (\k _ -> f k) ctx

sub_context set ctx =
  split_context (\x -> List.elem x set) ctx
