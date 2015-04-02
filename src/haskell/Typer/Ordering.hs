-- | This module is dedicated to finding the minimum of the partially ordered set formed by the type
-- variables, where the relation is given by the typing constraints.
--
-- * for every constraint /a/ <: /b/, the relation Age(/a/) = Age(/b/) is added
--
-- * for every constraint /a/ <: /T/ or /T/ <: /a/, a relation Age(/a/) < Age(/b/) is added for every
--   free type variable /b/ of /T/.
--
-- Variables are later organized in clusters (= equivalence classes) of variables with the same age,
-- and the relations between variables are changed into relations between the associated clusters.
-- The algorithm for finding the youngest cluster has a complexity of /O/(/n/), where /n/ is the number
-- of variables.
module Typer.Ordering where

import Parsing.Location (unknownExtent)
import Classes
import Utils

import Parsing.Location

import Core.Syntax
import Core.Printer

import Monad.Typer
import Monad.Error
import qualified Core.Namespace as N

import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Monad.Identity
import Data.List as List
import Data.IntMap as IntMap
import Data.IntSet as IntSet


-- | The type of a cluster.
type Cluster = Int


-- | Definition of posets (partially ordered sets). Inside of the poset, variables are grouped into
-- age classes (determined by atomic constraints), and the relations are written in term of such
-- classes.
data PosetContent = PosetContent {
  -- | Associates each variable to its respective cluster.
  assign :: IntMap Cluster,
  -- | For any given cluster, gives the related clusters (younger in age). For debugging purposes,
  -- the typing constraint from which the relation originated is added to each edge or relation.
  relations :: IntMap [(Cluster, TypeConstraint)],
  -- | The contents of each cluster.
  clusters :: IntMap [Variable]
}


-- | The current poset is passed in a state monad.
type Poset = StateT PosetContent Typer


-- | The empty poset.
empty :: PosetContent
empty = PosetContent {
  assign = IntMap.empty,
  relations = IntMap.empty,
  clusters = IntMap.empty
}


---------------------------------------------------------------------------------------------------
-- * Poset construction.

-- | Given a variable, find to which cluster it has been added. If the variable's cluster is undefined,
-- a new singleton cluster is created with the variable id as reference.
clusterOf :: Variable -> Poset Cluster
clusterOf x = do
  assign' <- gets assign
  case IntMap.lookup x assign' of
    Just c -> return c
    Nothing -> do
      -- Variable x is currently unassigned: create a singleton cluster to contain x.
      modify $ \poset ->
          poset { relations = IntMap.insert x [] $ relations poset,
                  clusters = IntMap.insert x [x] $ clusters poset,
                  assign = IntMap.insert x x $ assign poset }
      return x


-- | Return the contents of a cluster.
clusterContent :: Cluster -> Poset [Variable]
clusterContent c = do
  clusters <- gets clusters
  case IntMap.lookup c clusters of
    Just cts -> return cts
    Nothing -> fail $ "Ordering:clusterContent: undefined cluster: " ++ show c


-- | Return the list of younger clusters, according to the partial relation.
clusterRelations :: Cluster -> Poset [(Cluster, TypeConstraint)]
clusterRelations c = do
  relations <- gets relations
  case IntMap.lookup c relations of
    Just r -> return r
    Nothing -> return []


-- | Merge two clusters. The left cluster remains, and is augmented with the contents and relations
-- of the right one. All the references to the right cluster are also replaced by references to the
-- left.
mergeClusters :: Cluster -> Cluster -> Poset ()
mergeClusters c c' =
  -- If trying to merge the same cluster, do nothing.
  if c == c' then return ()
  else do
    -- Replace c' in the relations
    poset <- get
    let relations' =
          IntMap.map (List.map (\(d, cc) -> if d == c' then (c, cc) else (d, cc))) $ relations poset
    put $ poset { relations = relations' }
    -- Merge the relations and contents, and re-map the variables in c'.
    content <- clusterContent c
    rel <- clusterRelations c
    content' <- clusterContent c'
    rel' <- clusterRelations c'
    modify $ \poset ->
        poset {
          clusters = IntMap.update (\_ -> Just $ content ++ content') c $ IntMap.delete c' $ clusters poset,
          relations = IntMap.update (\_ -> Just $ rel ++ rel') c $ IntMap.delete c' $ relations poset,
          assign = IntMap.map (\d -> if d == c' then c else d) $ assign poset
        }


-- | Add an age relation between two clusters.
newRelation :: Cluster -> Cluster -> TypeConstraint -> Poset ()
newRelation c c' constraint =
  modify $ \poset -> poset { relations = IntMap.update (\r -> Just $ (c', constraint):r) c $ relations poset }


-- | Return 'True' if and only if no cluster remains.
nullPoset :: Poset Bool
nullPoset =
  gets $ IntMap.null . clusters


-- $ All the following functions are used for the construction \/ definition of the poset and its
-- relation. The relation is defined by the subtyping constraints:
--
-- * if the constraint is atomic /a/ <: /b/, then /a/ and /b/ must be of the same cluster, so merge
--   the clusters of /a/ and /b/.
--
-- * if the constraint is /a/ \<: /T/ or /T/ \<: /a/, for every free variable /b/ of /T/, add the
--   edge cluster(/b/) -\> cluster(/a/).


-- | Register a constraint and its consequences in the poset.
--
-- * If the constraint is atomic, then the two clusters of the type variables are merged.
--
-- * Otherwise, it is of the form /a/ <: /T/ or /T/ <: /a/. Relations are added from the cluster of
--   /a/ to the clusters of the free variables of /T/.
registerConstraint :: TypeConstraint -> Poset ()
registerConstraint constraint =
  case constraint of
    -- Case of an atomic constraint: merge the clusters of each variable.
    SubLinearType (TypeVar x) (TypeVar y) _ -> do
      cx <- clusterOf x
      cy <- clusterOf y
      mergeClusters cx cy

    -- Case of semi-composite constraints: add relations x <: y for every
    -- free variable y of u.
    SubLinearType (TypeVar x) u _ -> do
      cx <- clusterOf x
      IntSet.fold (\y rec -> do
          rec
          cy <- clusterOf y
          newRelation cy cx constraint
        ) (return ()) $ freevar u

    SubLinearType t (TypeVar x) _ -> do
      cx <- clusterOf x
      IntSet.fold (\y rec -> do
          rec
          cy <- clusterOf y
          newRelation cy cx constraint
        ) (return ()) $ freevar t

    SubLinearType _ _ _ ->
        throwNE $ ProgramError "Ordering:registerConstraint: illegal argument: unreduced constraint"

    Subtype _ _ _ ->
        throwNE $ ProgramError "Ordering:registerConstraint: illegal argument: unreduced constraint"


-- | Register a list of constraints.
registerConstraints :: [TypeConstraint] -> Poset ()
registerConstraints constraints = do
  List.foldl (\rec constraint -> do
      rec
      registerConstraint constraint
    ) (return ()) constraints


---------------------------------------------------------------------------------------------------
-- * Poset deconstruction.

-- | Return a randomly chosen cluster (fails if the poset is null).
someCluster :: Poset Cluster
someCluster = do
  clusters <- gets clusters
  case IntMap.keys clusters of
    [] -> throwNE $ ProgramError "Ordering:someCluster: illegal argument: []"
    (c: _) -> return c


-- | Explore the relations graph, starting from some cluster. The walk stops as soon as it finds a
-- cluster having no relatives (local minimum). If at some point it comes upon a cluster it had already
-- visited, that means there is a cycle in the graph: the poset is inconsistent, and builds an infinite
-- type. In this case, the walk fails.
findMinimum :: Cluster                     -- ^ Current cluster.
            -> [(TypeConstraint, Cluster)] -- ^ Historic of the walk.
            -> Poset Cluster               -- ^ A minimum cluster.
findMinimum current explored = do
  relations <- clusterRelations current
  case relations of
    -- No relation, this is a minimum !
    [] -> return current
    -- Relations found. Follow only the first one, as it can only end
    -- on either a minimum or a cyclic dependency.
    (cluster, constraint):_ -> do
      checkCyclic cluster $ (constraint, current):explored -- Check for cyclic dependencies.
      findMinimum cluster $ (constraint, current):explored -- Continue.


-- | An auxiliary function used by 'findMinimum'. Check whether a cluster appears in the list of
-- explored vertices. If it does, generate an error message that traces the cycle using the list of
-- dependencies. Otherwise, return ().
checkCyclic :: Cluster -> [(TypeConstraint, Cluster)] -> Poset ()
checkCyclic c explored = do
  case List.span (\(_, c') -> c /= c') explored of
    -- Ok, continue.
    (_, []) -> return ()
    -- Cyclic dependency !  (c' should be equal to c). Print out the constraints
    -- in the loop and fail.
    (loop, (constraint, c'):_) -> do
      -- Get all the constraints forming the loop.
      let cloop = List.map fst loop ++ [constraint]
      -- Identify the infinite type.
      let (var, info) = case constraint of
            SubLinearType (TypeVar x) _ info -> (x, info)
            SubLinearType _ (TypeVar x) info -> (x, info)
            _ -> throwNE $ ProgramError "Ordering:checkCyclic: unexpected unreduced constraint"
      -- Prepare printing options.
      poset <- get
      let fflag = \f -> ""
      let fvar = \x -> case IntMap.lookup x $ assign poset of
            Just c -> prevar "a" c
            Nothing -> prevar "x" x
      let falg = \a -> prevar "T" a -- displayUserType
      -- Print the loop and faulty variable.
      let loop = List.map (genprint Inf [fflag, fvar, falg]) cloop
          infinite = fvar var
      -- See what information we have. Print the expression and original type.
      --(ex, expr) <- ref_expression $ c_ref info
      --let original = case c_type info of
      --      Just a -> do
      --        p <- printType a
      --        return $ Just p
      --      Nothing -> return Nothing
      let original = Nothing
      let expr = "no location"
      let ext = unknownExtent
      throw (InfiniteTypeError infinite loop original expr) $ Just ext


-- | Find a minimum of a poset. This relies on the function 'findMinimum', applied to start on a
-- random cluster.
minimumCluster :: Poset Cluster
minimumCluster = do
  cluster <- someCluster
  minimum <- findMinimum cluster []
  --content <- clusterContent minimum
  return minimum


-- | Remove a cluster from a poset. All the relations involving this cluster are erased, and the
-- definition of the cluster is removed.
removeCluster :: Cluster -> Poset [Variable]
removeCluster cluster = do
  content <- clusterContent cluster
  modify $ \poset -> poset {
        assign = List.foldl (\m x -> IntMap.delete x m) (assign poset) content,
        relations = IntMap.map (List.filter (\(c', _) -> cluster /= c')) $ IntMap.delete cluster $ relations poset,
        clusters = IntMap.delete cluster $ clusters poset }
  return content


-- | Return the contents of a minimum cluster of a poset, after removing the said cluster definition
-- from the poset.
youngestVariables :: Poset [Variable]
youngestVariables = do
  cluster <- minimumCluster
  removeCluster cluster





-- | A type to hold a set with an equivalence relation. The variables are grouped into equivalence
-- classes.
data EqClasses a = EqClasses {
  assign' :: IntMap Int,                  -- ^ Map each variable to its respective equivalence class.
  classes :: IntMap ([Variable], [a])     -- ^ Contents of the equivalence classes.
}


-- | Same as posets, equivalence classes are passed in a state monad.
type Equiv a = StateT (EqClasses a) Identity


-- | Create a new set initialized with a list of variables that form the initial class. Note that
-- this list must not be empty.
newWithClass :: [Variable] -> EqClasses a
newWithClass [] = throwNE $ ProgramError "Ordering:newWithClass: illegal argument: []"
newWithClass c @ (a:_) =
  EqClasses {
      assign' = IntMap.fromList $ List.map (\b -> (b, a)) c,
      classes = IntMap.singleton a (c, [])
    }


-- | Return the equivalence class of a variable, or create one if it
-- does not exist.
classOf :: Variable -> Equiv a Int
classOf x = do
  assign <- gets assign'
  case IntMap.lookup x assign of
    Just c -> return c
    Nothing -> do
      modify $ \eqclasses -> eqclasses {
          assign' = IntMap.insert x x $ assign' eqclasses,
          classes = IntMap.insert x ([x],[]) $ classes eqclasses
        }
      return x


-- | Return the contents of a particular equivalence class.
classContents :: Int -> Equiv a ([Variable], [a])
classContents c = do
  classes <- gets classes
  case IntMap.lookup c classes of
    Just content -> return content
    Nothing -> return ([], [])


-- | Merge two equivalence classes, based on an equivalence relation passed as an argument.
mergeClasses :: Int -> Int -> a -> Equiv a ()
mergeClasses c c' a =
  if c == c' then
    modify $ \eqclasses -> eqclasses {
        classes = IntMap.update (\(content, as) -> Just (content, a:as)) c $ classes eqclasses }
  else do
    (content, as) <- classContents c
    (content', as') <- classContents c'
    modify $ \eqclasses -> eqclasses {
        assign' = IntMap.map (\d -> if d == c' then c else d) $ assign' eqclasses,
        classes = IntMap.update (\_ ->
            Just (content ++ content', a:(as ++ as'))
          ) c $ IntMap.delete c' $ classes eqclasses
      }


-- | Add a constraint relation to a set.
insertConstraint :: Variable -> Variable -> a -> Equiv a ()
insertConstraint x y a = do
  cx <- classOf x
  cy <- classOf y
  mergeClasses cx cy a


-- | Clean up a constraint set by removing the inaccessible flag and type constraints from a constraint
-- set, based on the variables appearing in the type. For example, assuming the type contains the flag
-- 0, and given the set
--
-- @
--  { 0 <= 2, 2 <= 3, 42 <= 24 },
-- @
--
-- the result will be the set { 0 <= 2, 2 <= 3 }. The constraint 42 <= 24, which cannot affect the type,
-- is removed.
cleanConstraintSet :: Type -> ConstraintSet -> ([Variable], [Flag], ConstraintSet)
cleanConstraintSet a (ConstraintSet lc fc) =
  let ff = IntSet.toList $ freeflag a
      fv = IntSet.toList $ freevar a in

  -- Clean the type constraints.
  let (ctsv, lc') = case fv of
        [] -> ([], [])
        (x:_) ->
          -- Computation in the equiv monad.
          let contents = do
                List.foldl (\rec c -> do
                    rec
                    case c of
                      SubLinearType (TypeVar x) (TypeVar y) _ -> insertConstraint x y c
                      _ -> throwNE $ ProgramError "Ordering:cleanConstraintSet: unexpected non-atomic constraint"
                  ) (return ()) lc
                cx <- classOf x
                classContents cx in
          -- Run the computation.
          fst $ runIdentity $ runStateT contents $ newWithClass fv in

  -- Clean the flag constraints
  let (ctsf, fc') = case ff of
        [] -> ([], [])
        (x:_) ->
          -- Computation in the equiv monad.
          let contents = do
                List.foldl (\rec c @ (Le n m _) -> do
                    rec
                    insertConstraint n m c
                  ) (return ()) fc
                cx <- classOf x
                classContents cx in
          -- Run the computation.
          fst $ runIdentity $ runStateT contents $ newWithClass ff in

  (ctsv, ctsf, ConstraintSet lc' fc')
