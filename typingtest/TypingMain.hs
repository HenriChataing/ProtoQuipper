module TypingMain where

import Classes
import Utils

import qualified Syntax as S
import CCoreSyntax
import CTransCore as Translate

import CContexts as Context
import CCTypeInference


type_inference :: S.Expr -> ConstraintSet
-----------------------------------------
type_inference e =
  let Translate.State run = do
      translateExpr (drop_constraints $ clear_location e)
  in
  let coreProg = snd $ run $ Translate.empty_context in

  let Context.State run = do
      a <- new_type
      constraints <- build_constraints coreProg a
      non_composite <- return $ break_composite constraints
      return non_composite
  in
  snd $ run $ Context.empty_context


full_inference :: S.Expr -> String
----------------------------------
full_inference e =
  let Translate.State run = do
      translateExpr (drop_constraints $ clear_location e)
  in
  let coreProg = snd $ run $ Translate.empty_context in

  let Context.State run = do
      a <- new_type
      constraints <- build_constraints coreProg a
      non_composite <- return $ break_composite constraints
      return non_composite
  in
  -- building constraints
  let (ctx, constraints) = run $ Context.empty_context in
  -- break composite constraints
  let reduced = break_composite constraints in
  -- infer age
  let ages = age_inference (fst reduced) (type_id ctx) in

  pprint_constraints reduced ++ "\n" ++ pprint_ages ages


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

