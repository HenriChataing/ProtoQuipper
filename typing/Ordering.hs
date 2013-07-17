module Ordering where

import Classes
import Utils
import Localizing
import QuipperError

import CoreSyntax
import CorePrinter

import QpState

import Data.List as List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap

-- |  This module (Ordering) is dedicated to finding the minimum of the poset formed
--  by the type variables, where the relation is given by the typing constraints.
--
--  As a reminder, for every constraint :
--
--    a <: b, the relation a = b is added
--    a <: T or T <: a, a relation a < b is added for every b free type variable of T
--
-- Variables are later organized in clusters (= classes) of variables with the same age,
-- and the relations between variables are changed into relations between the assiciated
-- clusters.
--
-- The algorithm for finding the youngest cluster (= set of youngest variables) has a complexity
-- O (n2) where n is the number of clusters, and in practice tries every cluster c, and checks
-- whether there is a relation c' < c, with c' another cluster.
--


-- | The type of a cluster id
type Cluster = Int


-- | Given a variable, finds to which cluster it has been added
-- If a cluster can't be found, a new cluster is created to contain
-- this variable, with an id equal to the variable id
cluster_of :: Type -> QpState Cluster
cluster_of ta@(TBang _ (TVar a)) = do
  ctx <- get_context
  case IMap.lookup a $ cmap ctx of
    Just c ->
        return c

    Nothing -> do
        set_context $ ctx { clusters = IMap.insert a [ta] $ clusters ctx,
                            cmap = IMap.insert a a $ cmap ctx }
        return a


-- | Returns the content of a cluster
cluster_content :: Cluster -> QpState [Type]
cluster_content c = do
  ctx <- get_context
  case IMap.lookup c $ clusters ctx of
    Just cts ->
        return cts

    Nothing ->
        throwQ $ ProgramError $ "cluster " ++ show c ++ " lacks an accompying definition"


-- | Merge two clusters
-- The left cluster remains, and is augmented with the contents of the right one
merge_clusters :: Cluster -> Cluster -> QpState ()
merge_clusters c c' = do
  if c == c' then
    -- If trying to merge the same cluster, do nothing
    return ()
  
  else do
    ctx <- get_context
    case (IMap.lookup c $ clusters ctx, IMap.lookup c' $ clusters ctx) of
      (Just cts, Just cts') -> do
          set_context $ ctx { cmap = IMap.map (\d -> if d == c' then c else d) $ cmap ctx,             -- All the variables of c' must know they are now part of c
                              clusters = IMap.insert c (cts ++ cts') $ IMap.delete c' $ clusters ctx,  -- Remove the cluster c', and transfer its contents to cluster c
                              relations = List.map (\(a, b) -> (if a == c' then c else a,
                                                                if b == c' then c else b)) $ relations ctx }  -- All the relations on c' are now relations on c

      -- In case one of the clusters is undefined
      (Nothing, _) ->
          throwQ $ ProgramError $ "cluster " ++ show c ++ " lacks an accompying definition"

      _ ->
          throwQ $ ProgramError $ "cluster " ++ show c' ++ " lacks an accompying definition"


-- | Add an age relation between two clusters
new_relation :: Cluster -> Cluster -> QpState ()
new_relation c c' = do
  ctx <- get_context
  set_context $ ctx { relations = (c, c'):(relations ctx) }


-- | Return the list of all defined relations
cluster_relations :: QpState [(Cluster, Cluster)]
cluster_relations = do
  get_context >>= return . relations


-- | Returns true iff the clusters map is empty
null_cluster :: QpState Bool
null_cluster = do
  ctx <- get_context
  return $ IMap.null $ clusters ctx



-- All the following functions are used for the construction / definition of the poset and its relation
-- The relation is defined by the subtyping constraints :
--      if the constraint is atomic a <: b, then a and b must be of the same cluster, so merge the clusters of a and b
--      if the constraint is a <: T or T <: a, for every b free_variable of T, add the relation cluster a < cluster b


-- | Returns the free type variables of a type, associated with their flag reference
free_var_with_flag :: Type -> [Type]
free_var_with_flag ta@(TBang _ (TVar _)) = [ta]
free_var_with_flag (TBang _ (TArrow t u)) = free_var_with_flag t ++ free_var_with_flag u
free_var_with_flag (TBang _ (TTensor tlist)) = List.concat $ List.map free_var_with_flag tlist
free_var_with_flag (TBang _ (TCirc t u)) = free_var_with_flag t ++ free_var_with_flag u 
free_var_with_flag _ = []


-- | Register a constraint and its consequences upon the poset
register_constraint :: TypeConstraint -> QpState ()
register_constraint c =
  case c of
    -- Case of an atomic constraint
    Subtype tx@(TBang _ (TVar _)) ty@(TBang _ (TVar _)) -> do
        cx <- cluster_of tx
        cy <- cluster_of ty
        -- Merge the clusters of x and y
        merge_clusters cx cy

    -- Case of semi composite constraints
    Subtype tx@(TBang _ (TVar _)) u -> do
        cx <- cluster_of tx
        fvu <- return $ free_var_with_flag u
        List.foldl (\rec ty -> do
                      rec
                      cy <- cluster_of ty
                      new_relation cx cy) (return ()) fvu
        
    Subtype t tx@(TBang _ (TVar _)) -> do
        cx <- cluster_of tx
        fvt <- return $ free_var_with_flag t
        List.foldl (\rec ty -> do
                      rec
                      cy <- cluster_of ty
                      new_relation cx cy) (return ()) fvt

    _ ->
        throwQ $ ProgramError $ "Unreduced composite constraint: " ++ pprint c


-- | Register a list of constraints
register_constraints :: [TypeConstraint] -> QpState ()
register_constraints clist = do
  List.foldl (\rec c -> do
                rec
                register_constraint c) (return ()) clist



-- All the following functions serve to find the youngest cluster / variables, given
-- the relation defined in the cluster

-- | Returns a randomly chosen cluster
some_cluster :: QpState Cluster
some_cluster = do
  ctx <- get_context
  case IMap.keys $ clusters ctx of
    [] ->
        throwQ $ ProgramError $ "empty cluster list"

    (c: _) ->
        return c


-- | Tests if the given cluster c is a minimum of the poset. It takes as input a cluster, and the list of processed clusters (all older than c). It returns
-- either the same cluster c if it was a minimum, or a new candidate c' taken from a relation c' < c. If the new candidate is in the list of processed
-- clusters, that means a cyclic dependency (infinite type)
try_cluster :: Cluster -> [Cluster] -> QpState (Cluster, [Cluster])
try_cluster c used = do
  rel <- cluster_relations

  List.foldl (\rec (t, u) -> do
                (c', used) <- rec
                if t == u then
                  fail "Cyclic dependency"
                else if c' == u then
                  if List.elem t used then
                    fail "Cyclic dependency"
                  else
                    return (t, c':used)
                else
                  return (c', used)) (return (c, used)) rel


-- | Using the function try_cluster, try every cluster until it finds a minimum of the poset, which it returns
find_youngest_cluster :: Cluster -> [Cluster] -> QpState Cluster
find_youngest_cluster c used = do
  (c', used') <- try_cluster c used
  if c == c' then
    return c
  else
    find_youngest_cluster c' used'


-- | Apply the function find_youngest_cluster with a random cluster, and an empty used cluster list 
youngest_cluster :: QpState Cluster
youngest_cluster = do
  c <- some_cluster
  c' <- find_youngest_cluster c []

  cts <- cluster_content c'

  -- Log the contents of the youngest cluster
  log_cts <- return $ List.foldl (\s x -> show x ++ " " ++ s) "" cts
  newlog 0 $ "\x1b[1m" ++ log_cts ++ "\x1b[0m"

  -- Return the youngest cluster
  return c'


-- | Remove the cluster from the system : erases the relations involving this cluster, and removes the definition of the cluster
remove_cluster :: Cluster -> QpState ()
remove_cluster c = do
  ctx <- get_context
  case IMap.lookup c $ clusters ctx of
    Just cts -> do
        set_context $ ctx { clusters = IMap.delete c $ clusters ctx,
                            cmap = List.foldl (\m (TBang _ (TVar x)) -> IMap.delete x m) (cmap ctx) cts,
                            relations = List.foldl (\r (t, u) -> if t == c || u == c then
                                                                   r
                                                                 else
                                                                   (t, u):r) [] $ relations ctx }
    Nothing ->
        return ()

                
-- | Returns the contents of the youngest cluster, after removing the cluster definition from the system
youngest_variables :: QpState [Type]
youngest_variables = do
  c <- youngest_cluster
  cts <- cluster_content c
  remove_cluster c
  return cts
