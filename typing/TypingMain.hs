module TypingMain where

import Classes
import Utils

import qualified Syntax as S
import Printer
import GenSTLC
import CoreSyntax
import TransSyntax

import Contexts
import TypeInference

import Data.List as List


type_inference :: S.Expr -> ConstraintSet
-----------------------------------------
type_inference e =
  let TransSyntax.State run = do
      translateExpr (drop_constraints $ clear_location e)
  in
  let coreProg = snd $ run $ TransSyntax.empty_context in

  let Contexts.State run = do
      a <- new_type
      constraints <- build_constraints coreProg a
      non_composite <- return $ break_composite constraints
      return non_composite
  in
  snd $ run $ Contexts.empty_context


full_inference :: S.Expr -> String
----------------------------------
full_inference e =
  let TransSyntax.State run = do
      translateExpr (drop_constraints $ clear_location e)
  in
  let coreProg = snd $ run $ TransSyntax.empty_context in

  let Contexts.State run = do
      a <- new_type
      constraints <- build_constraints coreProg a
      non_composite <- return $ break_composite constraints
      return non_composite
  in
  -- building constraints
  let (ctx, constraints) = run $ Contexts.empty_context in
  -- break composite constraints
  let reduced = break_composite constraints in
  -- infer age
  let ages = age_inference (fst reduced) (type_id ctx) in

  pprint_constraints reduced ++ "\n" ++ pprint_ages ages

-- Test of the inference on the exponential size typed term TWICE
test_full_inference :: Int -> String
-----------------------------
test_full_inference n =
  List.foldl (\s i -> let geni = generate_exp i in
                      let print_geni = pprint geni in
                      let pgeni = full_inference geni in
                      s ++ "-------------------------------------------\n" ++ print_geni ++ "\n" ++ pgeni) "" [0..n]

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

