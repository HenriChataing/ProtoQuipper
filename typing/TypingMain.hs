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
---------------------------------------------------------
gate_context gates = do
  List.foldl (\rec (s, t) -> do
                ctx <- rec
                (t', _) <- translate_type t [] (Map.empty)
                x <- gate_id s
                bind_var x t' ctx) (return IMap.empty) gates

full_inference :: S.Program -> IO String
----------------------------------
full_inference fprog =

  let run = do
      set_verbose 5

      prog <- translate_program fprog
      typctx <- gate_context typing_environment
  
      a <- new_type
      constraints <- constraint_typing typctx prog a
      non_composite <- break_composite constraints

      -- Unification
      register_constraints $ fst non_composite
      red_constraints <- unify non_composite

      inferred <- map_type a

      solve_annotation $ snd red_constraints
      valinf <- rewrite_flags inferred
      

      maps <- mapping_list
      pmaps <- List.foldl (\rec (x, t) -> do
                             s <- rec
                             return $ subvar 'X' x ++ " |-> " ++ pprint t ++ "\n" ++ s) (return "") maps

      return $ pprint constraints ++ "\n\n" ++
               pprint red_constraints ++ "\n\n" ++
               pmaps ++ "\n\n" ++
               pprint inferred ++ "\n\n" ++
               pprint valinf
  in do
    (_, s) <- runS run QpState.empty_context
    return s


-- Unification test
translate_list [] = do return []
translate_list ((t, u):l) = do
  t' <- translate_type t
  u' <- translate_type u
  l' <- translate_list l
  return $ (t', u'):l'

test_unification :: [(S.Type, S.Type)] -> IO String
------------------------------------------------ 
test_unification set =

  let run = do
      constraints <- List.foldl (\rec (t, u) -> do
                                   r <- rec
                                   (t', csett) <- translate_type t [] (Map.empty)
                                   (u', csetu) <- translate_type u [] (Map.empty)
                                   return $ [t' <: u'] <> csett <> csetu <> r) (return emptyset) set

      non_composite <- break_composite constraints

      -- Unification
      register_constraints $ fst non_composite
      red_constraints <- unify non_composite

      return $ pprint (constraints :: ConstraintSet) ++ "\n\n" ++
               pprint non_composite ++ "\n\n" ++
               pprint red_constraints
  in
  do
    (_, s) <- runS run QpState.empty_context
    return s

pprint_val :: Map Int Int -> String
------------------------------------
pprint_val val =
  Map.foldWithKey (\f n s -> s ++ " | " ++ subvar 'f' f ++ "=" ++ show n) "" val
