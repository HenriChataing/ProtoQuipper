-- | This module (Ordering) is dedicated to finding the minimum of the poset formed
-- by the type variables, where the relation is given by the typing constraints.
-- As a reminder, for every constraint:
--
-- *  a <: b, the relation Age (a) = Age(b) is added, and for every constraint
--
-- *  a <: T or T <: a, a relation Age (a) < Age (b) is added for every b free type variable of T.
--
-- Variables are later organized in clusters (= equivalence classes) of variables with the same age,
-- and the relations between variables are changed into relations between the associated
-- clusters. The algorithm for finding the youngest cluster has a complexity O (n) where n is the number of
-- variables.
module Typing.Ordering where

import Classes
import Utils

import Parsing.Localizing

import Typing.CoreSyntax
import Typing.CorePrinter

import Monad.QpState
import Monad.QuipperError

import Data.List as List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap


-- | The type of a cluster.
type Cluster = Int


-- | Definition of posets (partially ordered sets).
-- Inside of the poset, variables are grouped in age classes (built by atomic constraints), and the relations
-- are written in term of class.
data Poset = Poset {
  cmap :: IntMap Cluster,                                -- ^ Associates each variable to its respective cluster.

  relations :: IntMap [(Cluster, TypeConstraint)],       -- ^ For any given cluster, gives the related clusters (younger in age). For debugging purposes, the typing contraint
                                                         -- from which originated the relation is added to each edge or relation.

  clusters :: IntMap [Variable]                          -- ^ Gives the contents of each cluster.
}



-- | Empty poset.
empty_poset :: Poset
empty_poset = Poset {
  cmap = IMap.empty,
  relations = IMap.empty,
  clusters = IMap.empty
}



-- | Given a variable, finds to which cluster it has been added. If the variable's cluster is undefined, a new singleton cluster is created
-- with the variable id as reference.
cluster_of :: Variable -> Poset -> (Cluster, Poset)
cluster_of x poset =
  case IMap.lookup x $ cmap poset of
    Just c ->
        (c, poset)

    Nothing -> do
        (x, poset { relations = IMap.insert x [] $ relations poset,
                    clusters = IMap.insert x [x] $ clusters poset,
                    cmap = IMap.insert x x $ cmap poset })


-- | Returns the contents of a cluster.
cluster_contents :: Cluster -> Poset -> [Variable]
cluster_contents c poset =
  case IMap.lookup c $ clusters poset of
    Just cts ->
        cts

    Nothing ->
        fail $ "Cluster " ++ show c ++ " lacks an accompying definition"


-- | Returns the list of younger clusters, according to the partial relation.
cluster_relations :: Cluster -> Poset -> [(Cluster, TypeConstraint)]
cluster_relations c poset =
  case IMap.lookup c $ relations poset of
    Just r ->
        r

    Nothing ->
        []


-- | Merges two clusters. The left cluster remains, and is augmented with the contents and relations of the right one.
-- All the references to the right cluster are also replace by references to the left.
merge_clusters :: Cluster -> Cluster -> Poset -> Poset
merge_clusters c c' poset =
  if c == c' then
    -- If trying to merge the same cluster, do nothing
    poset
  
  else
    -- Replace c' in the relations
    let poset' = poset { relations = IMap.map (List.map (\(d, cc) -> if d == c' then (c, cc) else (d, cc))) $ relations poset } in

    let cts = cluster_contents c poset'
        r = cluster_relations c poset'
        cts' = cluster_contents c' poset'
        r' = cluster_relations c' poset' in
 
    poset' { clusters = IMap.update (\_ -> Just $ cts ++ cts') c (IMap.delete c' $ clusters poset'),
             relations = IMap.update (\_ -> Just $ r ++ r') c (IMap.delete c' $ relations poset'),
             cmap = IMap.map (\d -> if d == c' then c else d) $ cmap poset' }


-- | Adds an age relation between two clusters.
new_relation :: Cluster -> Cluster -> TypeConstraint -> Poset -> Poset
new_relation c c' cst poset =
  poset { relations = IMap.update (\r -> Just $ (c', cst):r) c $ relations poset }



-- | Returns true if and only if no cluster remains.
null_poset :: Poset -> Bool
null_poset poset =
  IMap.null $ clusters poset



-- All the following functions are used for the construction / definition of the poset and its relation
-- The relation is defined by the subtyping constraints :
--      if the constraint is atomic a <: b, then a and b must be of the same cluster, so merge the clusters of a and b
--      if the constraint is a <: T or T <: a, for every b free_variable of T, add the edge cluster b -> cluster a


-- | Returns the free type variables of a type, associated with their flag reference.
free_var_with_flag :: Type -> [Type]
free_var_with_flag ta@(TBang _ (TVar _)) = [ta]
free_var_with_flag (TBang _ (TArrow t u)) = free_var_with_flag t ++ free_var_with_flag u
free_var_with_flag (TBang _ (TTensor tlist)) = List.concat $ List.map free_var_with_flag tlist
free_var_with_flag (TBang _ (TCirc t u)) = free_var_with_flag t ++ free_var_with_flag u 
free_var_with_flag _ = []


-- | Registers a constraint and its consequences upon the poset.
-- 
-- * If the constraint is atomic, then the two clusters of the type variables are merged.
--
-- * Else it is of the form a <: T or T <: a. Relations are added from the cluster of a to the clusters of the free
-- variables of T.
--
register_constraint :: TypeConstraint -> Poset -> Poset
register_constraint cst poset =
  case cst of
    -- Case of an atomic constraint
    Sublintype (TVar x) (TVar y) _ ->
        let (cx, poset') = cluster_of x poset
            (cy, poset'') = cluster_of y poset' in
        -- Merge the clusters of x and y
        merge_clusters cx cy poset''

    -- Case of semi-composite constraints
    Sublintype (TVar x) u _ ->
        let (cx, poset') = cluster_of x poset
            fvu = free_typ_var u in
        List.foldl (\poset y ->
                      let (cy, poset') = cluster_of y poset in
                      new_relation cy cx cst poset') poset' fvu
        
    Sublintype t (TVar x) _ ->
        let (cx, poset') = cluster_of x poset
            fvt = free_typ_var t in
        List.foldl (\poset y ->
                      let (cy, poset') = cluster_of y poset in
                      new_relation cy cx cst poset') poset' fvt


-- | Registers a list of constraints.
register_constraints :: [TypeConstraint] -> Poset -> Poset
register_constraints clist poset =
  List.foldl (\poset c ->
                register_constraint c poset) poset clist



-- All the following functions serve to find the youngest cluster / variables, given
-- the relation defined in the cluster

-- | Returns a randomly chosen cluster (fails if the poset is null).
some_cluster :: Poset -> Cluster
some_cluster poset =
  case IMap.keys $ clusters poset of
    [] ->
        error "empty cluster list"

    (c: _) ->
        c


-- | Explores the relations graph, starting from some cluster.
-- The walk stops as soon as it finds a cluster having no relatives (local minimum).
-- If at some point it comes upon a cluster it had already visited, that means there is a
-- cycle in the graph: the poset is inconsistant, and builds an infinite type (the walk fails).
find_minimum :: Cluster                     -- ^ Current cluster.
             -> [(TypeConstraint, Cluster)] -- ^ Historic of the walk (all the explored clusters, and the relations that lead to them).
             -> Poset                       -- ^ The current poset.
             -> QpState Cluster             -- ^ A minimum cluster.
find_minimum c explored poset = do
  case cluster_relations c poset of
    -- No relation, this is a minimum !
    [] -> do
        return c

    -- Relations found. Follow only the first one, as it can only ends on either a minimum or a cyclic dependency.
    (c', cst):_ -> do
        -- Check for cyclic dependencies
        check_cyclic c' ((cst, c):explored) poset
        -- Continue
        find_minimum c' ((cst, c):explored) poset



-- | Function used exclusively in the find_minimum function. It checks whether a cluster appears in the list of explored vertices.
-- If it does, an error message is generated that traces the cycle using the list of dependencies, if not, it returns ().
check_cyclic :: Cluster -> [(TypeConstraint, Cluster)] -> Poset -> QpState ()
check_cyclic c explored poset = do
  case List.span (\(_, c') -> c /= c') explored of
    -- Ok
    (_, []) -> do
        return ()

    -- Cyclic dependency !  (c' should be equal to c)
    (loop, (cst, c'):_) -> do
        -- Put all the constraints one after the other
        cloop <- return $ List.map fst loop ++ [cst]
        -- Identify the infinite type
        (infinite, info) <- case cst of
                              Sublintype (TVar x) _ info -> return (x, info)
                              Sublintype _ (TVar x) info -> return (x, info)

        -- Printing flags
        refs <- get_context >>= return . flags
        fflag <- return (\f -> case f of
                                 1 -> "!"
                                 n | n >= 2 -> case IMap.lookup n refs of
                                                 Just fi -> case value fi of
                                                              One -> "!"
                                                              _ -> ""
                                                 Nothing -> ""
                                   | otherwise -> "")
        -- Printing variables : print the cluster instead
        fvar <- return (\x -> case IMap.lookup x $ cmap poset of
                                Just c -> subvar 'a' c
                                Nothing -> subvar 'x' x)

        ploop <- return $ List.map (\c -> genprint Inf c [fflag, fvar]) cloop
        prt <- return $ genprint Inf infinite [fflag, fvar]

        -- See what information we have
        -- Print the expression
        pre <- pprint_expr_noref $ expression info
        -- Print the original type
        mprt <- case in_type info of
                  Just a -> do
                      p <- pprint_lintype_noref a
                      return $ Just p
                  Nothing ->
                      return Nothing

        f <- get_file
        throwQ $ LocatedError (InfiniteTypeError prt ploop mprt pre) (f, loc info)




-- | Finds a minimum of a poset. It relies on the function find_minimum, applied to start on a random cluster.
minimum_cluster :: Poset -> QpState Cluster
minimum_cluster poset = do
  c <- return $ some_cluster poset
  cm <- find_minimum c [] poset

  cts <- return $ cluster_contents cm poset

  -- Log the contents of the youngest cluster
  lastflag <- get_context >>= return . flag_id
  log_cts <- return $ List.foldl (\s x -> show x ++ " " ++ s) "" (lastflag:cts)
  newlog 1 $ "\x1b[1m" ++ log_cts ++ "\x1b[0m"

  -- Return the youngest cluster
  return cm


-- | Removes a cluster from a poset: all the relations involving this cluster are erased, the definition of the cluster removed.
remove_cluster :: Cluster -> Poset -> ([Variable], Poset)
remove_cluster c poset =
  let cts = cluster_contents c poset in
  (cts, poset { cmap = List.foldl (\m x -> IMap.delete x m) (cmap poset) cts,
                relations = IMap.map (List.filter (\(c', _) -> c /= c')) $ IMap.delete c $ relations poset,
                clusters = IMap.delete c $ clusters poset })

                
-- | Returns the contents of a minimum cluster of a poset, after removing the said cluster definition from the poset.
youngest_variables :: Poset -> QpState ([Variable], Poset)
youngest_variables poset = do
  c <- minimum_cluster poset
  return $ remove_cluster c poset


