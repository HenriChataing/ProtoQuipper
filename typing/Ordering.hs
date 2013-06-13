module Ordering where

import Classes
import Utils
import Localizing

import CoreSyntax
import Contexts

import Subtyping

import Data.List as List
import Data.Sequence as Seq
import Data.Array as Array
import qualified Data.Map as Map
import qualified Data.Set as Set

-- ============================== --
-- ==== Cluster manipulation ==== --

cluster_of :: Variable -> State Int
new_cluster :: Variable -> State ()
cluster_content :: Int -> State [Variable]
merge_clusters :: Int -> Int -> State ()
new_relation :: Int -> Int -> State ()
add_variable :: Variable -> State ()
null_cluster :: State Bool
----------------------------------------
cluster_of x =
  State (\ctx -> (ctx, case Map.lookup x $ ages ctx of
                         Just c -> return c
                         Nothing -> fail ("Unassigned variable " ++ show x) ))

cluster_content x =
  State (\ctx -> (ctx, case Map.lookup x $ clusters ctx of
                         Just c -> return c
                         Nothing -> fail "Cluster lacks an accompying definition"))

new_cluster x =
  State (\ctx -> (ctx { clusters = Map.insert x [x] $ clusters ctx,
                        ages = Map.insert x x $ ages ctx }, return ()))

merge_clusters x y =
  State (\ctx -> if x == y then
                   (ctx, return ())
                 else
                   case (Map.lookup x $ clusters ctx, Map.lookup y $ clusters ctx) of
                     (Just cx, Just cy) ->
                         (ctx { ages = Map.map (\z -> if z == y then x else z) $ ages ctx,
                                clusters = Map.insert x (cx ++ cy) $ Map.delete y $ clusters ctx,
                                relations = List.map (\(a, b) -> (if a == y then x else a,
                                                                if b == y then x else b)) $ relations ctx }, return ())
                     _ ->
                         (ctx, fail ("Cluster #" ++ show x ++ "lacks a defintion")))

new_relation x y =
  State (\ctx -> (ctx { relations = (x, y):(relations ctx) }, return ()))

add_variable x =
  State (\ctx -> (ctx { variables = x:(variables ctx),
                        clusters = Map.insert x [x] $ clusters ctx,
                        ages = Map.insert x x $ ages ctx }, return ())) 

null_cluster =
  State (\ctx -> (ctx, return $ Map.null $ clusters ctx))

-- Create an empty graph, with as each variable assigned to a different vertex
init_ordering :: State ()
-------------------------
init_ordering =
  State (\ctx -> let n = type_id ctx in
           (ctx { variables = [0 .. type_id ctx - 1],
                  relations = [],
                  clusters = Map.fromList $ List.map (\x -> (x, [x])) [0 .. type_id ctx - 1],
                  ages = Map.fromList $ List.map (\x -> (x, x)) [0 .. type_id ctx - 1] }, return ()))

-- Add all the relations introduced by a sub-typing constraint
register_constraint :: LinearConstraint -> State ()
register_constraints :: [LinearConstraint] -> State ()
cluster_relations :: State [(Int, Int)]
---------------------------------------------------
register_constraint c = do
  case c of
    (TVar x, TVar y) -> do
        cx <- cluster_of x
        cy <- cluster_of y
        merge_clusters cx cy

    (TVar x, u) -> do
        cx <- cluster_of x
        fvu <- return $ free_var u
        List.foldl (\e y -> do
                      e
                      cy <- cluster_of y
                      new_relation cx cy
                      return ()) (return ()) fvu
        
    (t, TVar x) -> do
        cx <- cluster_of x
        fvt <- return $ free_var t
        List.foldl (\e y -> do
                      e
                      cy <- cluster_of y
                      new_relation cx cy
                      return ()) (return ()) fvt

    _ -> fail ("Unreduced composite constraint (" ++ pprint c ++ ")")

register_constraints [] = return ()
register_constraints (c:cc) = do
  register_constraint c
  register_constraints cc

cluster_relations =
  State (\ctx -> (ctx, return $ relations ctx))

-- ================================ --
-- ====== Variable selection ====== --

some_cluster :: State Int   -- Return an arbitrary cluster
try_cluster :: Int -> [Int] -> State (Int, [Int])
find_youngest_cluster :: Int -> [Int] -> State Int
youngest_cluster :: State Int
remove_cluster :: Int -> State ()
youngest_variables :: State [Variable]
--------------------------------------
some_cluster =
  State (\ctx -> (ctx, case Map.keys $ clusters ctx of
                         [] -> fail "Empty cluster list"
                         (c:_) -> return c))

try_cluster c used = do
  rel <- cluster_relations

  List.foldl (\rec (t, u) -> do
                           (yg, used) <- rec
                           if t == u then
                             fail "Cyclic dependency"
                           else if yg == u then
                             if List.elem t used then
                               fail "Cyclic dependency"
                             else
                               return (t, yg:used)
                           else
                             return (yg, used)) (return (c, [])) rel

find_youngest_cluster c used = do
  (c', used') <- try_cluster c used
  if c == c' then
    return c
  else
    find_youngest_cluster c' used'

youngest_cluster = do
  c <- some_cluster
  yg <- find_youngest_cluster c []

  cyg <- cluster_content yg
  log_yg <- return $ List.foldl (\s x -> show x ++ " " ++ s) "" cyg
  create_log log_yg
  return yg

remove_cluster x =
  State (\ctx -> case Map.lookup x $ clusters ctx of 
                   Just xc ->
                       (ctx { variables = (variables ctx) \\ xc,
                              clusters = Map.delete x $ clusters ctx,
                              ages = List.foldl (\ag y -> Map.delete y ag) (ages ctx) xc,
                              relations = List.foldl (\r (t, u) -> if List.elem t xc || List.elem u xc then
                                                                     r
                                                                   else
                                                                     (t, u):r) [] $ relations ctx }, return ())
                   _ ->
                       (ctx, return ()))
                        
youngest_variables = do
  x <- youngest_cluster
  cx <- cluster_content x
  remove_cluster x
  return cx
