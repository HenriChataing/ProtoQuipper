module TypingMain where

import Classes
import Utils

import qualified Syntax as S
import Printer
import CoreSyntax
import TransSyntax

import Gates

import Subtyping
import Ordering

import Contexts
import TypeInference

import Data.List as List
import Data.Map as Map

-- Import the gates into the current context
import_gates :: [(String, S.Type)] -> State ()
----------------------------------------------
import_gates gates = do
  List.foldl (\rec (s, t) -> do
                rec
                t' <- translate_type t
                x <- label s
                bind_var x t') (return ()) gates

full_inference :: S.Expr -> String
----------------------------------
full_inference e =

  let Contexts.State run = do
      import_gates $ typing_environment
      prog <- translate_expression (drop_constraints $ clear_location e)

      a <- new_type
      constraints <- constraint_typing prog a
      non_composite <- break_composite constraints

      -- Unification
      init_ordering
      register_constraints $ fst non_composite
      red_constraints <- unify non_composite
      logs <- print_logs

      inferred <- map_type a

      sol <- solve_annotation $ snd red_constraints
      valinf <- app_val_to_type inferred sol
      

      maps <- mapping_list
      pmaps <- List.foldl (\rec (x, t) -> do
                             s <- rec
                             return $ (subscript $ "X" ++ show x) ++ " |-> " ++ pprint t ++ "\n" ++ s) (return "") maps

      return $ pprint constraints ++ "\n\n" ++
               pprint red_constraints ++ "\n\n" ++
               pmaps ++ "\n\n" ++
               pprint_val sol ++ "\n\n" ++
               pprint inferred ++ "\n\n" ++
               pprint valinf ++ "\n\n" ++
               logs
  in
  
  case snd $ run $ Contexts.empty_context of
    Ok s -> s
    Failed err -> show err


-- Unification test
translate_list [] = do return []
translate_list ((t, u):l) = do
  t' <- translate_type t
  u' <- translate_type u
  l' <- translate_list l
  return $ (t', u'):l'

test_unification :: [(S.Type, S.Type)] -> String
------------------------------------------------ 
test_unification set =

  let Contexts.State run = do
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
      logs <- print_logs

      return $ pprint ((constraints, []) :: ConstraintSet) ++ "\n\n" ++
               pprint non_composite ++ "\n\n" ++
               pprint red_constraints ++ "\n\n" ++
               logs
  in

  case snd $ run $ Contexts.empty_context of
    Ok s -> s
    Failed err -> show err

pprint_val :: Map Int Int -> String
------------------------------------
pprint_val val =
  Map.foldWithKey (\f n s -> s ++ " | " ++ subscript ("f" ++ show f) ++ "=" ++ show n) "" val
