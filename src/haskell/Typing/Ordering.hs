-- | This module is dedicated to finding the minimum of the partially ordered set formed
-- by the type variables, where the relation is given by the typing constraints.
-- As a reminder:
--
-- * for every constraint /a/ <: /b/, the relation Age(/a/) = Age(/b/) is added, and
--
-- * for every constraint /a/ <: /T/ or /T/ <: /a/, a relation Age(/a/) < Age(/b/) is added for every free type variable /b/ of /T/.
--
-- Variables are later organized in clusters (= equivalence classes) of variables with the same age,
-- and the relations between variables are changed into relations between the associated
-- clusters. The algorithm for finding the youngest cluster has a complexity of /O/(/n/), where /n/ is the number of
-- variables.
module Typing.Ordering where

import Classes
import Utils

import Parsing.Location

import Core.Syntax
import Core.Printer

import Monad.QpState
import Monad.QuipperError
import qualified Monad.Namespace as N

import Data.List as List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap


-- | The type of a cluster.
type Cluster = Int


-- | Definition of posets (partially ordered sets).
-- Inside of the poset, variables are grouped into age classes (determined by atomic constraints), and the relations
-- are written in term of such classes.
data Poset = Poset {
  cmap :: IntMap Cluster,                                -- ^ Associates each variable to its respective cluster.

  relations :: IntMap [(Cluster, TypeConstraint)],       -- ^ For any given cluster, gives the related clusters (younger in age). For debugging purposes, the typing constraint
                                                         -- from which the relation originated is added to each edge or relation.

  clusters :: IntMap [Variable]                          -- ^ The contents of each cluster.
}



-- | The empty poset.
empty_poset :: Poset
empty_poset = Poset {
  cmap = IMap.empty,
  relations = IMap.empty,
  clusters = IMap.empty
}



-- | Given a variable, find to which cluster it has been added. If the variable's cluster is undefined, a new singleton cluster is created
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


-- | Return the contents of a cluster.
cluster_contents :: Cluster -> Poset -> [Variable]
cluster_contents c poset =
  case IMap.lookup c $ clusters poset of
    Just cts ->
        cts

    Nothing ->
        fail $ "Ordering:cluster_contents: undfined cluster: " ++ show c


-- | Return the list of younger clusters, according to the partial relation.
cluster_relations :: Cluster -> Poset -> [(Cluster, TypeConstraint)]
cluster_relations c poset =
  case IMap.lookup c $ relations poset of
    Just r ->
        r

    Nothing ->
        []


-- | Merge two clusters. The left cluster remains, and is augmented with the contents and relations of the right one.
-- All the references to the right cluster are also replaced by references to the left.
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


-- | Add an age relation between two clusters.
new_relation :: Cluster -> Cluster -> TypeConstraint -> Poset -> Poset
new_relation c c' cst poset =
  poset { relations = IMap.update (\r -> Just $ (c', cst):r) c $ relations poset }



-- | Return 'True' if and only if no cluster remains.
null_poset :: Poset -> Bool
null_poset poset =
  IMap.null $ clusters poset



-- $ All the following functions are used for the construction \/ definition of the poset and its relation.
-- The relation is defined by the subtyping constraints:
--
-- * if the constraint is atomic /a/ <: /b/, then /a/ and /b/ must be of the same cluster, so merge the clusters of /a/ and /b/.
--
-- * if the constraint is /a/ \<: /T/ or /T/ \<: /a/, for every free variable /b/ of /T/, add the edge cluster(/b/) -\> cluster(/a/).


-- | Register a constraint and its consequences in the poset.
--
-- * If the constraint is atomic, then the two clusters of the type variables are merged.
--
-- * Otherwise, it is of the form /a/ <: /T/ or /T/ <: /a/. Relations are added from the cluster of /a/ to the clusters of the free
-- variables of /T/.
register_constraint :: TypeConstraint -> Poset -> Poset
register_constraint cst poset =
  case cst of
    -- Case of an atomic constraint
    SubLinearType (TypeVar x) (TypeVar y) _ ->
        let (cx, poset') = cluster_of x poset
            (cy, poset'') = cluster_of y poset' in
        -- Merge the clusters of x and y
        merge_clusters cx cy poset''

    -- Case of semi-composite constraints
    SubLinearType (TypeVar x) u _ ->
        let (cx, poset') = cluster_of x poset
            fvu = free_typ_var u in
        List.foldl (\poset y ->
                      let (cy, poset') = cluster_of y poset in
                      new_relation cy cx cst poset') poset' fvu

    SubLinearType t (TypeVar x) _ ->
        let (cx, poset') = cluster_of x poset
            fvt = free_typ_var t in
        List.foldl (\poset y ->
                      let (cy, poset') = cluster_of y poset in
                      new_relation cy cx cst poset') poset' fvt

    SubLinearType _ _ _ ->
        throwNE $ ProgramError "Ordering:register_constraint: illegal argument: unreduced constraint"

    Subtype _ _ _ ->
        throwNE $ ProgramError "Ordering:register_constraint: illegal argument: unreduced constraint"

-- | Register a list of constraints.
register_constraints :: [TypeConstraint] -> Poset -> Poset
register_constraints clist poset =
  List.foldl (\poset c ->
                register_constraint c poset) poset clist



-- All the following functions serve to find the youngest cluster / variables, given
-- the relation defined in the cluster

-- | Return a randomly chosen cluster. This function fails with an error if the poset is null.
some_cluster :: Poset -> Cluster
some_cluster poset =
  case IMap.keys $ clusters poset of
    [] ->
        throwNE $ ProgramError "Ordering:some_cluster: illegal argument: []"

    (c: _) ->
        c


-- | Explore the relations graph, starting from some cluster.
-- The walk stops as soon as it finds a cluster having no relatives (local minimum).
-- If at some point it comes upon a cluster it had already visited, that means there is a
-- cycle in the graph: the poset is inconsistent, and builds an infinite type. In this case, the walk fails.
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



-- | An auxiliary function used by 'find_minimum'. Check whether a cluster appears in the list of explored vertices.
-- If it does, generate an error message that traces the cycle using the list of dependencies. Otherwise, return ().
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
                              SubLinearType (TypeVar x) _ info -> return (x, info)
                              SubLinearType _ (TypeVar x) info -> return (x, info)
                              _ -> throwNE $ ProgramError "Ordering:check_cyclic: unexpected unreduced constraint"
        -- Printing flags
        fflag <- return (\f -> "")

        -- Printing variables : print the cluster instead
        fvar <- return (\x -> case IMap.lookup x $ cmap poset of
                                Just c -> prevar "a" c
                                Nothing -> prevar "x" x)
        -- Printing type names
        falg <- display_algebraic
        ploop <- return $ List.map (genprint Inf [fflag, fvar, falg]) cloop
        prt <- return $ fvar infinite

        -- See what information we have
        -- Print the expression
        (ex, expr) <- ref_expression $ c_ref info
        -- Print the original type
        mprt <- case c_type info of
                  Just a -> do
                      p <- pprint_type_noref a
                      return $ Just p
                  Nothing ->
                      return Nothing

        throwQ (InfiniteTypeError prt ploop mprt expr) ex




-- | Find a minimum of a poset. This relies on the function 'find_minimum', applied to start on a random cluster.
minimum_cluster :: Poset -> QpState Cluster
minimum_cluster poset = do
  c <- return $ some_cluster poset
  cm <- find_minimum c [] poset

  cts <- return $ cluster_contents cm poset

  -- Log the contents of the youngest cluster
--  lastflag <- get_context >>= return . flag_id
--  log_cts <- return $ List.foldl (\s x -> show x ++ " " ++ s) "" (lastflag:cts)
--  newlog 1 $ "\x1b[1m" ++ log_cts ++ "\x1b[0m"

  -- Return the youngest cluster
  return cm


-- | Remove a cluster from a poset. All the relations involving this cluster are erased, and the definition of the cluster is removed.
remove_cluster :: Cluster -> Poset -> ([Variable], Poset)
remove_cluster c poset =
  let cts = cluster_contents c poset in
  (cts, poset { cmap = List.foldl (\m x -> IMap.delete x m) (cmap poset) cts,
                relations = IMap.map (List.filter (\(c', _) -> c /= c')) $ IMap.delete c $ relations poset,
                clusters = IMap.delete c $ clusters poset })


-- | Return the contents of a minimum cluster of a poset, after removing the said cluster definition from the poset.
youngest_variables :: Poset -> QpState ([Variable], Poset)
youngest_variables poset = do
  c <- minimum_cluster poset
  return $ remove_cluster c poset





-- | A type to hold a set with an equivalence relation.
-- The variables are grouped into equivalence classes.
data Equiv a = Eqv {
  clmap :: IntMap Int,                     -- ^ Map each variable to its respective equivalence class.
  classes :: IntMap ([Variable], [a])      -- ^ Contents of the equivalence classes.
}


-- | Create a new set initialized with a list of variables that form the initial class.
-- Note that this list must not be empty.
new_with_class :: [Variable] -> Equiv a
new_with_class c@(a:_) =
  Eqv { clmap = IMap.fromList $ List.map (\b -> (b, a)) c,
        classes = IMap.singleton a (c, []) }
new_with_class [] =
  throwNE $ ProgramError "Ordering:new_with_class: illegal argument: []"


-- | Return the equivalence class of a variable, or create one if it
-- does not exist.
in_class :: Variable -> Equiv a -> (Int, Equiv a)
in_class x eqv =
  case IMap.lookup x $ clmap eqv of
    Just c -> (c, eqv)
    Nothing -> (x, eqv { clmap = IMap.insert x x $ clmap eqv,
                         classes = IMap.insert x ([x],[]) $ classes eqv })


-- | Return the contents of a particular equivalence class.
class_contents :: Int -> Equiv a -> ([Variable], [a])
class_contents c eqv =
  case IMap.lookup c $ classes eqv of
    Just cts -> cts
    Nothing -> ([], [])


-- | Merge two equivalence classes, based on an equivalence relation passed as an argument.
merge_classes :: Int -> Int -> a -> Equiv a -> Equiv a
merge_classes c c' a eqv =
  if c /= c' then
    let (cts, as) = class_contents c eqv
        (cts', as') = class_contents c' eqv in
    eqv { clmap = IMap.map (\d -> if d == c' then c else d) $ clmap eqv,
          classes = IMap.update (\_ -> Just (cts ++ cts', a:(as ++ as'))) c $ IMap.delete c' $ classes eqv }
  else
    eqv { classes = IMap.update (\(cts, as) -> Just (cts, a:as)) c $ classes eqv }


-- | Add a constraint relation to a set.
insert_constraint :: Variable -> Variable -> a -> Equiv a -> Equiv a
insert_constraint x y c eqv =
  let (cx, eqv') = in_class x eqv
      (cy, eqv'') = in_class y eqv' in
  merge_classes cx cy c eqv''


-- | Clean up a constraint set by removing
-- the inaccessible flag and type constraints from a constraint set, based on the variables
-- appearing in the type. For example, assuming the type contains the flag 0, and given the set
--
-- @
--  { 0 <= 2, 2 <= 3, 42 <= 24 },
-- @
--
-- the result will be the set { 0 <= 2, 2 <= 3 }. The constraint 42 <= 24, which cannot affect the type,
-- is removed.
clean_constraint_set :: Type -> ConstraintSet -> ([Variable], [Flag], ConstraintSet)
clean_constraint_set a (lc, fc) =
  let ff = free_flag a
      fv = free_typ_var a in

  -- Clean the type constraints
  let (ctsv, lc') = case fv of
                     [] -> ([], [])
                     (x:_) -> let eqvl = new_with_class fv in
                              let eqvl' = List.foldl (\eqv c ->
                                                       case c of
                                                         SubLinearType (TypeVar x) (TypeVar y) _ ->
                                                           insert_constraint x y c eqv
                                                         _ -> throwNE $ ProgramError "Ordering:clean_constraint_set: unexpected non-atomic constraint"
                                                     ) eqvl lc in
                              let (cl, _) = in_class x eqvl' in
                              class_contents cl eqvl' in

  -- Clean the flag constraints
  let (ctsf, fc') = case ff of
                     [] -> ([], [])
                     (x:_) -> let eqvf = new_with_class ff in
                              let eqvf' = List.foldl (\eqv c@(Le n m _) ->
                                                        insert_constraint n m c eqv) eqvf fc in
                              let (cf, _) = in_class x eqvf' in
                              class_contents cf eqvf' in

  (ctsv, ctsf, (lc', fc'))

