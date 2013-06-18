module TypingMain where

import Classes
import Utils

import qualified Syntax as S
import Printer
import CoreSyntax
import TransSyntax

import Subtyping
import Ordering

import Contexts
import TypeInference

import Data.List as List
import Data.Map as Map

full_inference :: S.Expr -> String
----------------------------------
full_inference e =
  let TransSyntax.State run = do
      gates <- translate_gates
      prog <- translate_expression (drop_constraints $ clear_location e)
      return (gates, prog)
  in
  let (gates, coreProg) = snd $ run $ TransSyntax.empty_context in

  let Contexts.State run = do
      import_gates gates
      a <- new_type
      constraints <- constraint_typing coreProg a
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

  let TransSyntax.State run = do
      translate_list set
  in

  let trans = run $ TransSyntax.empty_context in
  let core_set = List.map (\(t, u) -> NonLinear t u) (snd trans) in

  let Contexts.State run = do
      constraints <- return (core_set, [])
      non_composite <- break_composite constraints

      -- Unification
      init_ordering
      register_constraints $ fst non_composite
      red_constraints <- unify non_composite
      logs <- print_logs

      return $ pprint constraints ++ "\n\n" ++
               pprint non_composite ++ "\n\n" ++
               pprint red_constraints ++ "\n\n" ++
               logs
  in

  case snd $ run $ Contexts.empty_context { type_id = var_id $ fst $ trans } of
    Ok s -> s
    Failed err -> show err

pprint_val :: Map Int Int -> String
------------------------------------
pprint_val val =
  Map.foldWithKey (\f n s -> s ++ " | " ++ subscript ("f" ++ show f) ++ "=" ++ show n) "" val
