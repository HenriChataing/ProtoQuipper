module TypingMain where

import Localizing (clear_location)
import Classes
import Utils

import qualified Syntax as S
import Printer
import CoreSyntax
import TransSyntax

import Gates

import Subtyping
import Ordering

import QpState
import TypingContext
import TypeInference

import Data.List as List
import Data.Map as Map

-- Import the gates into the current context
gate_context :: [(String, S.Type)] -> QpState TypingContext
---------------------------------------------------------
gate_context gates = do
  List.foldl (\rec (s, t) -> do
                ctx <- rec
                t' <- translate_type t
                x <- label s
                bind_var x t' ctx) (return Map.empty) gates

full_inference :: S.Expr -> IO String
----------------------------------
full_inference e =

  let run = do
      typctx <- gate_context typing_environment
      prog <- translate_expression (drop_constraints $ clear_location e)

      a <- new_type
      constraints <- constraint_typing typctx prog a
      non_composite <- break_composite constraints

      -- Unification
      init_ordering
      register_constraints $ fst non_composite
      red_constraints <- unify non_composite

      inferred <- map_type a

      sol <- solve_annotation $ snd red_constraints
      valinf <- app_val_to_type inferred sol
      

      maps <- mapping_list
      pmaps <- List.foldl (\rec (x, t) -> do
                             s <- rec
                             return $ subvar 'X' x ++ " |-> " ++ pprint t ++ "\n" ++ s) (return "") maps

      return $ pprint constraints ++ "\n\n" ++
               pprint red_constraints ++ "\n\n" ++
               pmaps ++ "\n\n" ++
               pprint_val sol ++ "\n\n" ++
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
                                   t' <- translate_type t
                                   u' <- translate_type u
                                   return $ (NonLinear t' u'):r) (return []) set

      non_composite <- break_composite (constraints, [])

      -- Unification
      init_ordering
      register_constraints $ fst non_composite
      red_constraints <- unify non_composite

      return $ pprint ((constraints, []) :: ConstraintSet) ++ "\n\n" ++
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
