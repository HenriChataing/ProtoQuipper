module TypeInference where

import CoreSyntax

import Contexts

import Classes
import Utils

import Data.List as List
import Data.Sequence as Seq
import Data.Array as Array
import qualified Data.Map as Map
import qualified Data.Set as Set

-------------------------
-- Various constraints --

type LinearConstraint =         
  (Type, Type)      -- T <: U

type FlagConstraint =
  (Flag, Flag)      -- n <= m

type ConstraintSet =
  ([LinearConstraint], [FlagConstraint])

-----------------------------------------------------------------
-----------------------------------------------------------------

-- Build all the deriving constraints
build_constraints :: Expr -> Type -> State ConstraintSet

-- Unit typing rule
{-
    ---------------------
      !I G  |- * : !n T    {1 <= I} 
-} 

build_constraints EUnit t = do
  ann <- flag_annotations
  return ([(t, TUnit)], List.map (\(_, f) -> (1, f)) ann)
  
-- Var typing rule
{-
     
   ------------------------------------------
     !IG, t : T |- t : U    {T <: U, 1 <= I} 
-}

build_constraints (EVar x) u = do
  t <- CContexts.find x
  ann <- flag_annotations
  ann' <- return $ List.deleteBy (\(x, _) (y, _) -> x == y) (x, 0) ann
  return ([(t, u)], List.map (\(_, f) -> (1, f)) ann')

-- App typing rule
{-
     G1, !ID |- t : a -> T  {L, C}       G2, !ID |- u : a  {L', C'}
   -----------------------------------------------------------------
         G1, G2, !ID |- t u : T  {L u L', C u C' u 1 <= I}
-}

build_constraints (EApp t u) b = do
  a <- fresh_type
  -- Extract the free variables of t and u
  fvt <- return $ free_variables t
  fvu <- return $ free_variables u
  -- Filter on the free variables of t and type t
  non_fvt <- CContexts.filter (\x -> List.elem x fvt)
  (lcons, fcons) <- build_constraints t (TArrow (TVar a) b)
  -- Filter on the free variables of u and type u
  CContexts.union non_fvt
  non_fvu <- CContexts.filter (\x -> List.elem x fvu)
  (lcons', fcons') <- build_constraints u (TVar a)
  -- Reset the environment, and add the last constraints
    -- Need to perform : FV(t) + FV(u) (disjoint union)
  CContexts.union non_fvu
  dis_union <- return $ List.union (fvt \\ fvu) (fvu \\ fvt)
  ann <- flag_annotations
  ann_cons <- return $ List.foldl (\cl (x, f) -> if List.elem x dis_union then cl
                                                 else (1, f):cl) [] ann
  
  return (lcons' ++ lcons, fcons' ++ fcons ++ ann_cons)

-- Lambda typing rule
{-
     !IG, x : a |- t : b  {L, C}
   ---------------------------------------------
     !IG |- \x.t : !n(a -> b)  {L, C u n <= Ii}
-}

build_constraints (EFun x e) t = do
  a <- new_annotated_type
  b <- new_type
  n <- fresh_flag
  ann <- flag_annotations
  -- Bind x in the context
  bind x a
  -- Type the expression e
  (lcons, fcons) <- build_constraints e b
  -- Build the context constraints : n <= I
  ann_cons <- return $ List.map (\(_, f) -> (n, f)) ann
  -- Remove x from the context
  CContexts.delete x

  return ((TExp n $ TArrow a b, t):lcons, fcons ++ ann_cons)

--------------------------------------------------------------------------
--------------------------------------------------------------------------

-- Break composite constrainst of the form :
  -- T -> U <: T' -> U'
  -- ! T <: ! U

break_composite :: ConstraintSet -> ConstraintSet

-- Nothing to do
break_composite ([], lc) = ([], lc)

-- Break constraints
  -- T -> U <: T' -> U' 
-- Into
  -- T' <: T && U <: U'
break_composite ((TArrow t u, TArrow t' u'):lc, fc) =
  break_composite ((t', t):(u, u'):lc, fc)

-- Break constraints
  -- !n T <: !m U
-- Into
  -- T <: U && m <= n
break_composite ((TExp n t, TExp m u):lc, fc) =
  break_composite ((t, u):lc, (m, n):fc)

-- Break constraints
  -- !n T <: U
-- Into
  -- T <: U
break_composite ((TExp _ t, u):lc, fc) =
  break_composite ((t, u):lc, fc)

-- Break constraints
  -- T <: !n U
-- Into
  -- T <: U && n <= 0
break_composite ((t, TExp n u):lc, fc) =
  break_composite ((t, u):lc, (n, 0):fc)

-- Other non composite constraints
break_composite (c:lc, fc) =
  let (lc', fc') = break_composite (lc, fc) in
  (c:lc', fc')

--------------------------------------------------------------------------
--------------------------------------------------------------------------

-- Determining the age of the type variables :
  -- if there is a subtyping relation a <: T then a is younger than any
  -- free type variable of T
-- The goal is to sort variables by their age, and rule out cyclic dependencies

data Vertex =
  Vertex {
    incoming :: Set.Set Variable,
    outcoming :: Set.Set Variable
  }

-- The diagram definition includes :
  -- a graph definition
  -- an exploration queue
  -- a set of visited points
data Diagram =
  Graph {
    vertices :: Array Variable Vertex,
    start :: Seq Variable,
    visit :: Set.Set Variable 
  }

-- Result of a computation
data Compute a = Ok a | Error String
instance Monad Compute where
  return a = Ok a
  fail s = Error s
  a >>= action = case a of
                   Ok a -> action a
                   Error s -> Error s

-- State monad
newtype Build a = Build (Diagram -> (Diagram, Compute a))

instance Monad Build where
  return a = Build (\dia -> (dia, Ok a))
  Build run >>= action = Build (\dia -> let (dia', a) = run dia in
                                        case a of
                                          Ok a -> let Build run' = action a in
                                                  run' dia'
                                          Error s -> (dia, Error s))
  fail s = Build (\dia -> (dia, Error s))


-- Diagram containing the vertices from 0 to n, and no edges
init_diagram :: Int -> Diagram
-----------i-------------------
init_diagram n =
  Graph {
    vertices = Array.array (0, n-1)  -- Array index bounds
                           (List.map (\ix -> (ix, Vertex { incoming = Set.empty, outcoming = Set.empty })) [0..n-1]),
    start = empty,
    visit = Set.empty
  }

-- Add a new edge to the diagram, point from the first variable to the second
new_edge :: Variable -> Variable -> Build ()
new_edges :: Variable -> [Variable] -> Build ()
--------------------------------------------
new_edge v1 v2 =
  Build (\dia -> let vx1 = vertices dia ! v1
                     vx2 = vertices dia ! v2 in
                 (dia { vertices = (vertices dia) // [(v1, vx1 { outcoming = Set.insert v2 $ outcoming vx1 }),
                                                      (v2, vx2 { incoming = Set.insert v1 $ incoming vx2 })] }, Ok ()))

new_edges v1 [] = return ()
new_edges v1 (v2:cv2) = do
  new_edge v1 v2
  new_edges v1 cv2

-- Find the root vertices, towards which no edge points
find_roots :: Build [Variable]
---------------------------
find_roots =
  Build (\dia -> let roots = List.foldl (\roots (i, e) -> if Set.null $ incoming e then
                                                            i:roots
                                                          else
                                                            roots) [] $ assocs $ vertices dia in
                 case roots of
                   [] -> (dia, fail "Error : cyclic dependency detected in the constraint set")
                   _ -> (dia, return roots))

-- Give the vertices pointing to, or starting from, a vertex
incoming_edges :: Variable -> Build [Variable]
outcoming_edges :: Variable -> Build [Variable]
----------------------------------------
incoming_edges v =
  Build (\dia -> (dia, return $ Set.toList $ incoming $ (vertices dia) ! v))
outcoming_edges v =
  Build (\dia -> (dia, return $ Set.toList $ outcoming $ (vertices dia) ! v))

-- Remove all edges starting from this vertex
cut_vertex :: Variable -> Build ()
----------------------------------
cut_vertex v =
  Build (\dia -> let dest = outcoming $ (vertices dia) ! v in
                 let vertices' = Set.fold (\d ary -> let inc = incoming $ ary ! d in
                                                     ary // [(d, (ary ! d) { incoming = Set.delete v inc })])
                                          (vertices dia) dest in
                 (dia { vertices = vertices' }, return ()))

-- Find the new roots
filter_roots :: [Variable] -> Build [Variable]
----------------------------------------------
filter_roots vs =
  Build (\dia -> (dia, return $ List.foldl (\filt v -> if Set.null $ incoming $ (vertices dia) ! v then
                                                         (v:filt)
                                                       else
                                                         filt) [] vs))

-- Queue management
is_queue_empty :: Build Bool
next :: Build Variable
put :: [Variable] -> Build ()
-----------------------------
is_queue_empty =
  Build (\dia -> (dia, return $ Seq.null $ start dia))
next =
  Build (\dia -> case viewr $ start dia of
                   EmptyR -> (dia, fail "Empty queue")
                   seq :> v -> (dia { start = seq }, return v))
put vl =
  Build (\dia -> (dia { start = (fromList vl) >< (start dia) }, return ()))

---- Main Function : bfs ----
type Age = Int

-- Bfs walk
bfs_walk :: Map.Map Variable Age -> Build (Map.Map Variable Age)
--------------------------------------------------------
bfs_walk records = do
  v <- next
  agev <- case Map.lookup v records of
            Just a -> return a
            Nothing -> fail ("No age recorded for variable " ++ show v)
  -- Outcoming edges of v
  out <- outcoming_edges v
  -- Remove any edge pointing from v
  -- Filter the new roots (no incoming edge)
  cut_vertex v
  out' <- filter_roots out
  -- Define the age of the new roots
  records' <- List.foldl (\rec v' -> do
                              r <- rec
                              agev' <- return $ Map.lookup v' r
                              case agev' of
                                Nothing -> return $ Map.insert v' (agev + 1) r
                                Just _ -> fail "Cyclic dependency in constraint set") (return $ records) out'
  -- Put the new roots in the queue
  put out'

  -- Recursive call
  empt <- is_queue_empty
  if not empt then
    bfs_walk records'
  else
    return records'

-- Init the walk : find the roots and define their age
init_walk :: Build (Map.Map Variable Age)
-----------------------------------------
init_walk = do
  roots <- find_roots
  records <- return $ List.foldl (\rec r -> Map.insert r 0 rec) Map.empty roots
  put roots
  return records

-- Create edges from constraints
create_edges :: [LinearConstraint] -> Build ()
----------------------------------------------
create_edges [] = return ()
create_edges (c:cl) = do
    case c of
      -- a <: b   --> atomic constraint
      (TVar _, TVar _) -> return ()
      -- a <: T
      (TVar x, u) -> do
          fvu <- return $ free_type_variables u
          new_edges x fvu
      -- T <: a
      (t, TVar x) -> do
          fvt <- return $ free_type_variables t
          new_edges x fvt
      -- composite
      (t, u) -> fail ("Error : unreduced composite constraint : " ++ pprint t ++ " <: " ++ pprint u)
    create_edges cl


-- Infer the age of the type variables       (second arg is number of type variables
age_inference :: [LinearConstraint] -> Variable -> Compute (Map.Map Variable Age)
-----------------------------------------------------------------------------
age_inference constraints n =
  let init = init_diagram n in
  
  let Build run = do
      -- Add the initial edges
        -- for each constraint a <: T or T <: a, a is declared younger than any free variable of T
      create_edges constraints

      -- Init the walk
      records <- init_walk

      -- Launch the walk
      records' <- bfs_walk records

      -- Return the result
      return records' 
  in

  snd $ run init

-- Print age map
pprint_ages :: Compute (Map.Map Variable Age) -> String
-------------------------------------------------------
pprint_ages map =
  case map of
    Error s -> s
    Ok m -> Map.foldWithKey (\v a s -> s ++ subscript ("X" ++ show v) ++ " @ " ++ show a ++ "\n") "" m 

