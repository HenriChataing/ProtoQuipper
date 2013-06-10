module Contexts where

import CoreSyntax
import Localizing

import Classes
import Utils

import qualified Data.Map as Map
import Data.List as List
import Data.Array as Array
import qualified Data.Set as Set
import Data.Sequence as Seq 

{- Representation of a graph vertex.
  The data structure includes a set of incoming and a set of outgoing
  edges. The walk in the graph follows the outgoing edges, while the
  incoming ones serve to decide whether the vertex is a root vertex or not
-}
data Vertex =
  Vertex {
    incoming :: Set.Set Variable,
    outgoing :: Set.Set Variable
  }

-------------------------
-- Contexts definition --

data Context =
  Ctx {
    --
    -- LOG
    --

    logfile :: [String],

    --
    -- ID GENERATION
    --

    type_id :: Int, 
    flag_id :: Int,

    --
    --  CONSTRAINT BUILDING STUFF
    --

    -- Map of bindings : Term variable -> Type
    bindings :: Map.Map Int Type,

    --
    -- VARIABLE DATING STUFF
    --

    -- Vertices of the graph
    vertices :: Array Variable Vertex,
    -- The set of the roots of the graph
    roots :: Seq Variable,
    -- The result of the datation is a list of the variables, sorted from youngest to oldest
    heuristic :: [Variable],

    --
    -- UNIFICATION STUFF
    --

    -- Substitution from type variable to types
    mappings :: Map.Map Variable Type
  }
newtype State a = State (Context -> (Context, Computed a))

instance Monad State where
  return a = State (\ctx -> (ctx, Ok a))
  fail s = State (\ctx -> (ctx, Failed $ CustomError s extent_unknown))
  State run >>= action = State (\ctx -> let (ctx', a) = run ctx in
                                        case a of
                                          Ok a -> let State run' = action a in
                                                  run' ctx'
                                          Failed err -> (ctx', Failed err))


-- Create an empty context (without the basic gates)
empty_context :: Context
------------------------
empty_context =
  Ctx {
    logfile = [">> Log start <<"],
    bindings = Map.empty,

    vertices = Array.array (0,0) [],
    roots = Seq.empty,
    heuristic = [],

    flag_id = 2,   -- Flag ids 0 and 1 are reserved, and represent the values 0 and 1
    type_id = 0,
      
    mappings = Map.empty
  }

-- ========================== --
-- ===== Id generation ====== --

fresh_type :: State Variable
fresh_flag :: State Flag

-- Number of generated type variables
ntypes :: State Int

-- Generate a type of the form a or !n a 
new_type :: State Type
new_annotated_type :: State Type

--------------------------------

fresh_type = State (\ctx -> (ctx { type_id = (+1) $ type_id ctx }, Ok $ type_id ctx))
fresh_flag = State (\ctx -> (ctx { flag_id = (+1) $ flag_id ctx }, Ok $ flag_id ctx))

ntypes = State (\ctx -> (ctx, Ok $ type_id ctx))

new_type = do
  x <- fresh_type
  return (TVar x)

new_annotated_type = do
  x <- fresh_type
  f <- fresh_flag
  return (TExp f $ TVar x)

-- =========================== --
-- === Context annotations === --

-- Return the flag annotation of the context, as a list of associations (term * flag)
context_annotation :: State [(Variable, Flag)]
----------------------------------------------
context_annotation = State (\ctx -> (ctx, Ok $  Map.foldWithKey (\x t ann -> case t of
                                                                               TExp f _ -> (x, f):ann
                                                                               TUnit -> (x, 1):ann
                                                                               _ -> error ("No flag annotation specified for the type of " ++ subscript ("x" ++ show x)))
                                                                [] $ bindings ctx))

-- ============================ --
-- === Context manipulation === --

-- Add a new bindings (var * type) in the current typing context
bind_var :: Variable -> Type -> State ()
-- Find the type given to a variable
find_var :: Variable -> State Type
-- Remove a variable from the context
delete_var :: Variable -> State ()
-- Filter on the variables contained in the context
filter_by :: (Variable -> Bool) -> State (Map.Map Variable Type)  -- Select a part of the bindings and return the unselected part
-- Insert a set of bindings
union :: (Map.Map Variable Type) -> State ()
---------------------------------------------------------
bind_var x t = State (\ctx -> (ctx { bindings = Map.insert x t $ bindings ctx }, return ()))

find_var x = State (\ctx -> (ctx, case Map.lookup x $ bindings ctx of
                                Just t -> return t
                                Nothing -> fail ("Unbound variable " ++ subscript ("x" ++ show x))))

delete_var x = State (\ctx -> (ctx { bindings = Map.delete x $ bindings ctx }, return ()))

filter_by f = State (\ctx -> let (ptrue, pfalse) = Map.partitionWithKey (\x _ -> f x) $ bindings ctx in
                          (ctx { bindings = ptrue }, return pfalse))

union m = State (\ctx -> (ctx { bindings = Map.union m $ bindings ctx }, return ()))

-- ============================== --
-- ===== Variable ordering ====== --

-- Init the preferred order list
set_heuristic :: [Variable] -> State ()
-- Get and remove the first variable in the list
fitting_var :: State Variable
-- Set the new preferred variable
new_fitting :: Variable -> State ()
-- Test whether the preference list is empty
null_heuristic :: State Bool
-- Insert variables in the queue
insert_after :: Variable -> [Variable] -> State ()
insert_all_after :: [Variable] -> [Variable] -> State ()
--------------------------------------------------------
set_heuristic ord =
  State (\ctx -> (ctx { heuristic = ord }, return ()))

fitting_var =
  State (\ctx -> case heuristic ctx of
                   [] -> (ctx, fail "Prefered order list is empty")
                   x:xc -> (ctx { heuristic = xc }, return x))

new_fitting x =
  State (\ctx -> (ctx { heuristic = x:(heuristic ctx) }, return ()))

null_heuristic = 
  State (\ctx -> (ctx, return $ heuristic ctx == []))
                   
insert_after x l =
  State (\ctx -> let insert = \h -> case h of
                                         [] -> [x]
                                         (y:hc) -> if List.elem y l then
                                                     (x:y:hc)
                                                   else
                                                     (y:(insert hc))
                 in
                 (ctx { heuristic = List.reverse (insert $ List.reverse $ heuristic ctx) }, return ()))

insert_all_after [] l = do return ()
insert_all_after (v:cv) l = do
  insert_after v l
  insert_all_after cv l


-- =============================== --
-- ========= Substitution ======== --

-- Insert a new mapping in the substitution
mapsto :: Variable -> Type -> State ()
-- Find the type a variable is mapped to
appmap :: Variable -> State Type
-- Apply the mappings to a type
map_type :: Type -> State Type   -- Caution : this function disregards the flag annotations when subs. (!n t) in (!m x)
------------------------------
mapsto x t = State (\ctx -> (ctx { mappings = Map.insert x t $ mappings ctx }, return ()))

appmap x = State (\ctx -> (ctx, case Map.lookup x $ mappings ctx of
                                  Just t -> return t
                                  _ -> return $ TVar x))

map_type (TVar x) = do
  appmap x

map_type (TArrow t u) = do
  t' <- map_type t
  u' <- map_type u
  return (TArrow t' u')

map_type (TTensor t u) = do
  t' <- map_type t
  u' <- map_type u
  return (TTensor t' u')

map_type (TExp n t) = do
  t' <- map_type t
  -- In this line : possible collision between the flag n and the flag of t' (if any)
  return (TExp n t')

------------------------
-- Some printing --

instance Show Context where
  show ctx = "[| " ++ (Map.foldWithKey (\k t s -> s ++ subscript ("x" ++ show k) ++ " : " ++ pprint t ++ "\n") "" $ bindings ctx) 
 
