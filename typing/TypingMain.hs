module TypingMain where

import Localizing (clear_location)
import Classes
import Utils

import qualified Syntax as S
import Printer
import CoreSyntax
import TransSyntax

import Gates

import Ordering

import QpState
import TypingContext
import TypeInference

import Data.List as List
import Data.Map as Map
import Data.IntMap as IMap

-- Import the gates into the current context
gate_context :: [(String, S.Type)] -> QpState TypingContext
gate_context gates = do
  List.foldl (\rec (s, t) -> do
                ctx <- rec
                (t', _) <- translate_type t [] (Map.empty)
                x <- gate_id s
                bind_var x t' ctx) (return IMap.empty) gates


-- | Type inference algorithm
-- This is the main function of the inference, which puts together all the different part of the algorithm
-- It is to be called on a surface program, and it returns the inferred type.
-- If the expression is not typable, it fails with a 'appropriate' error message.
-- The boolean argument indicates whether an exact solution is expected, or if approximations can be made, giving
-- only one specific (not most general) type
type_inference :: Bool -> S.Program -> QpState Type
type_inference exact fprog = do
  -- Translation into core syntax
  prog <- translate_program fprog
  
  -- Create the initial typing context
  typctx <- gate_context typing_environment
  
  -- Create the initial type
  a <- new_type

  -- | constraint typing | --
  constraints <- constraint_typing typctx prog a
  newlog 0 ">> Initial constraint set"
  newlog 0 $ pprint constraints ++ "\n"

  -- | Unification | --
  constraints <- break_composite True constraints
    -- For ordering purposes
  register_constraints $ fst constraints
  constraints <- unify exact constraints
  newlog 0 ">> Unified constraint set"
  newlog 0 $ pprint constraints ++ "\n"

  -- Application of the solution map to the initial type
  inferred <- map_type a
  newlog 0 $ ">> Inferred type : " ++ pprint inferred

  -- Solve the remaining flag constraints,
  -- and apply the result to the inferred type to get the final answer
  solve_annotation $ snd constraints
  inferred <- rewrite_flags inferred
  newlog 0 $ ">> Inferred type, references removed : " ++  pprint inferred ++ "\n"

  -- Same with the export variables
  ctx <- get_context
  exp <- return $ IMap.assocs $ export ctx
  exp <- List.foldl (\rec (x, a) -> do
                       r <- rec
                       a' <- map_type a
                       a' <- rewrite_flags a'
                       return ((x, a'):r)) (return []) exp

  newlog 0 ">> Export variables"
  List.foldl (\rec (x, a) -> do
                rec
                newlog 0 $ subvar 'x' x ++ " :: " ++ pprint a) (return ()) exp
  newlog 0 "<<\n"
  
  -- Return the inferred type 
  return inferred


-- | A unification test : the unification alogorithm is run
-- on a set of typing constraints. It doesn't return anything, 
-- but prints the constraint after the unification
unification_test :: [(S.Type, S.Type)] -> IO String
unification_test set =
  let run = do
      -- Translate the types in the internal syntax
      constraints <- List.foldl (\rec (t, u) -> do
                                   r <- rec
                                   (t', csett) <- translate_type t [] (Map.empty)
                                   (u', csetu) <- translate_type u [] (Map.empty)
                                   return $ [t' <: u'] <> csett <> csetu <> r) (return emptyset) set

      -- Run the unification algorithm
      constraints <- break_composite True constraints

      -- Unification
      register_constraints $ fst constraints
      constraints <- unify True constraints

      return $ pprint constraints
  in
  do
    (_, s) <- runS run QpState.empty_context
    return s

