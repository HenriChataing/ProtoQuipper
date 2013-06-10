module TypingMain where

import Classes
import Utils

import qualified Syntax as S
import Printer
import GenSTLC
import CoreSyntax
import TransSyntax

import Subtyping
import Ordering

import Contexts
import TypeInference

import Data.List as List
import Data.Map as Map

type_inference :: S.Expr -> Computed ConstraintSet
-----------------------------------------
type_inference e =
  let TransSyntax.State run = do
      translate_expression (drop_constraints $ clear_location e)
  in
  let coreProg = snd $ run $ TransSyntax.empty_context in

  let Contexts.State run = do
      a <- new_type
      constraints <- build_constraints coreProg a
      non_composite <- break_composite constraints
      return non_composite
  in
  snd $ run $ Contexts.empty_context


full_inference :: S.Expr -> String
----------------------------------
full_inference e =
  let TransSyntax.State run = do
      translate_expression (drop_constraints $ clear_location e)
  in
  let coreProg = snd $ run $ TransSyntax.empty_context in

  let Contexts.State run = do
      a <- new_type
      constraints <- build_constraints coreProg a
      non_composite <- break_composite constraints

      order_variables $ fst non_composite

      red_constraints <- unify non_composite

      sol <- solve_annotation $ snd red_constraints

      return $ pprint_constraints constraints ++ "\n\n" ++
               pprint_constraints non_composite ++ "\n\n" ++
               pprint_constraints red_constraints ++ "\n\n" ++
               pprint_val sol
  in
  
  case snd $ run $ Contexts.empty_context of
    Ok s -> s
    Failed err -> show err

-- Test of the inference on the exponential size typed term TWICE
test_full_inference :: Int -> String
-----------------------------
test_full_inference n =
  List.foldl (\s i -> let geni = generate_exp i in
                      let print_geni = pprint geni in
                      let pgeni = full_inference geni in
                      s ++ "-------------------------------------------\n" ++ print_geni ++ "\n" ++ pgeni) "" [0..n]

-- Unification test
translate_list [] = do return []
translate_list ((t, u):l) = do
  t' <- translate_type t
  u' <- translate_type u
  l' <- translate_list l
  return $ (t', u'):l'

show_heuristic :: Contexts.State String
show_heuristic = Contexts.State (\ctx -> (ctx, return $ List.foldl (\s h -> s ++ " " ++ show h) "" $ heuristic ctx))

test_unification :: [(S.Type, S.Type)] -> String
------------------------------------------------ 
test_unification set =

  let TransSyntax.State run = do
      translate_list set
  in

  let trans = run $ TransSyntax.empty_context in
  let core_set = snd $ trans in

  let Contexts.State run = do
      constraints <- return (core_set, [])
      non_composite <- break_composite constraints

      order_variables $ fst non_composite

      red_constraints <- unify non_composite
      heuristic <- show_heuristic

      return $ pprint_constraints constraints ++ "\n\n" ++
               pprint_constraints non_composite ++ "\n\n" ++
               heuristic ++ "\n\n" ++
               pprint_constraints red_constraints
  in

  case snd $ run $ Contexts.empty_context { type_id = var_id $ fst $ trans } of
    Ok s -> s
    Failed err -> show err

---------------------------------------------
pprint_constraints :: ConstraintSet -> String
---------------------------------------------

pprint_constraints ((t, u):lc, fc) =
  pprint t ++ " <: " ++ pprint u ++ "\n" ++
  pprint_constraints (lc, fc)

pprint_constraints ([], (n, m):fc) =
  (if n >= 2 then subscript ("f" ++ show n) else show n) ++ " <= " ++
  (if m >= 2 then subscript ("f" ++ show m) else show m) ++ "\n" ++
  pprint_constraints ([], fc)

pprint_constraints ([], []) =
 ""

pprint_val :: Map Flag Int -> String
------------------------------------
pprint_val val =
  Map.foldWithKey (\f n s -> s ++ " | " ++ subscript ("f" ++ show f) ++ "=" ++ show n) "" val
