module Ordering where

import Classes
import Utils
import Localizing

import CoreSyntax
import QpState

import Subtyping

import Data.List as List
import qualified Data.Map as Map

{-
  This module (Ordering) is dedicated to finding the minimum of the poset formed
  by the type variables, where the relation is given by the typing constraints.

  As a reminder, for every constraint :

    - a <: b, the relation a = b is added
    - a <: T or T <: a, a relation a < b is added for every b free type variable of T

  Variables are later organized in clusters (= classes) of variables with the same age,
  and the relations between variables are changed into relations between the assiciated
  clusters.
  
  The algorithm for finding the youngest cluster (= set of youngest variables) has a complexity
  O (n2) where n is the number of clusters, and in practice tries every cluster c, and checks
  whether there is a relation c' < c, with c' another cluster.

  The following functions are :
    - cluster_of : returns the cluster the variable is part of
    - new_cluster : creates a new singleton cluster (with the same as the variable)
    - cluster_content : returns the variable content of a cluster
    - merge_clusters : merge two clusters, and do the necessary changes (typically used when coming upon a constraint a <: b)
    - new_relation : extend the partial relation with c < c'
    - add_variable : insert a new variable in the system, and creates a new matching cluster at the same time
    - null_cluster : checks whether the number of clusters is 0
    - cluster_relations : returns the partial relations
-}

type Cluster = Int

cluster_of :: Variable -> QpState Cluster
new_cluster :: Variable -> QpState ()
cluster_content :: Cluster -> QpState [Variable]
merge_clusters :: Cluster -> Cluster -> QpState ()
new_relation :: Cluster -> Cluster -> QpState ()
add_variable :: Cluster -> QpState ()
null_cluster :: QpState Bool
cluster_relations :: QpState [(Cluster, Cluster)]
----------------------------------------
cluster_of x =
  QpState (\ctx -> case Map.lookup x $ ages ctx of
                   Just c -> return (ctx, c)
                   Nothing -> fail ("Unassigned variable " ++ show x))

cluster_content x =
  QpState (\ctx -> case Map.lookup x $ clusters ctx of
                   Just c -> return (ctx, c)
                   Nothing -> fail "Cluster lacks an accompying definition")

new_cluster x =
  QpState (\ctx -> return (ctx { clusters = Map.insert x [x] $ clusters ctx,
                               ages = Map.insert x x $ ages ctx }, ()))

merge_clusters x y =
  QpState (\ctx -> if x == y then
                   return (ctx, ())
                 else
                   case (Map.lookup x $ clusters ctx, Map.lookup y $ clusters ctx) of
                     (Just cx, Just cy) ->
                         return (ctx { ages = Map.map (\z -> if z == y then x else z) $ ages ctx,
                                       clusters = Map.insert x (cx ++ cy) $ Map.delete y $ clusters ctx,
                                       relations = List.map (\(a, b) -> (if a == y then x else a,
                                                                         if b == y then x else b)) $ relations ctx }, ())
                     _ ->
                         fail ("Cluster #" ++ show x ++ "lacks a defintion"))

new_relation x y =
  QpState (\ctx -> return (ctx { relations = (x, y):(relations ctx) }, ()))

add_variable x =
  QpState (\ctx -> return (ctx { variables = x:(variables ctx),
                               clusters = Map.insert x [x] $ clusters ctx,
                               ages = Map.insert x x $ ages ctx }, ())) 

null_cluster =
  QpState (\ctx -> return (ctx, Map.null $ clusters ctx))

cluster_relations =
  QpState (\ctx -> return (ctx, relations ctx))


{-
  Construction of the poset, with two functions to instanciate the poset, and insert new relations defined by
  typing constraints.

  - init_ordering : inserts all the type variables in the ordering system
  - register_constraint / register_constraints : following the forma of the constraint :
     - if the constraint is atomic : a <: b, then a and b must be in the same cluster, so merge the clusters of a and b
     - if the constraint is a <: T or T <: a, for every b free variable of T, add the relation cluster a < cluster b
-}

init_ordering :: QpState ()
register_constraint :: TypeConstraint -> QpState ()
register_constraints :: [TypeConstraint] -> QpState ()
----------------------------------------------------
init_ordering =
  QpState (\ctx -> let n = type_id ctx in
           return (ctx { variables = [0 .. type_id ctx - 1],
                         relations = [],
                         clusters = Map.fromList $ List.map (\x -> (x, [x])) [0 .. type_id ctx - 1],
                         ages = Map.fromList $ List.map (\x -> (x, x)) [0 .. type_id ctx - 1] }, ()))

register_constraint c = do
  case c of
    Linear (TVar x) (TVar y) -> do
        cx <- cluster_of x
        cy <- cluster_of y
        merge_clusters cx cy

    Linear (TVar x) u -> do
        cx <- cluster_of x
        fvu <- return $ free_var u
        List.foldl (\e y -> do
                      e
                      cy <- cluster_of y
                      new_relation cx cy
                      return ()) (return ()) fvu
        
    Linear t (TVar x) -> do
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


{-
  Core of the algorithm :
  
  - some_cluster : returns any cluster
  - try_cluster : returns True iff the cluster is a minimum. It takes as input a cluster, and the list of processed clusters, and
                  returns either the same cluster if it was a minimum, or a new candidate deduced from the relation that forbade c as a minimum.
                  If the new candidate is in the list of processed clusters, that means a cyclic dependency === trying to build an infinite type
  - find_youngest_cluster : try every cluster, starting from a random one, until it finds a minimum, which it returns
  - youngest_cluster :
  - remove_cluster : remove the cluster from the system : erases the relations involving this cluster, removes the definition of the cluster..
  - younngest_variables : same as youngest_cluster, only it returns the contents of the youngest cluster

-}
some_cluster :: QpState Cluster
try_cluster :: Cluster -> [Cluster] -> QpState (Cluster, [Cluster])
find_youngest_cluster :: Cluster -> [Cluster] -> QpState Cluster
youngest_cluster :: QpState Cluster
remove_cluster :: Cluster -> QpState ()
youngest_variables :: QpState [Variable]
--------------------------------------
some_cluster =
  QpState (\ctx -> case Map.keys $ clusters ctx of
                   [] -> fail "Empty cluster list"
                   (c:_) -> return (ctx, c))

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
  new_log $ "\x1b[1m" ++ log_yg ++ "\x1b[0m"
  return yg

remove_cluster x =
  QpState (\ctx -> case Map.lookup x $ clusters ctx of 
                   Just xc ->
                       return (ctx { variables = (variables ctx) \\ xc,
                                     clusters = Map.delete x $ clusters ctx,
                                     ages = List.foldl (\ag y -> Map.delete y ag) (ages ctx) xc,
                                     relations = List.foldl (\r (t, u) -> if List.elem t xc || List.elem u xc then
                                                                            r
                                                                          else
                                                                            (t, u):r) [] $ relations ctx }, ())
                   _ ->
                       return (ctx, ()))
                        
youngest_variables = do
  x <- youngest_cluster
  cx <- cluster_content x
  remove_cluster x
  return cx
