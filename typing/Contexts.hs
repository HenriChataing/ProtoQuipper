module Contexts where

import CoreSyntax
import Localizing

import Classes
import Utils

import Subtyping

import qualified Data.Map as Map
import Data.List as List
import Data.Array as Array
import qualified Data.Set as Set
import Data.Sequence as Seq 

-------------------------
-- Contexts definition --

data Context =
  Ctx {
    --
    -- LOG
    --

    log_enabled :: Bool,
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

    -- Variable classes
    variables :: [Variable],
    relations :: [(Int, Int)],
    clusters :: Map.Map Int [Variable],  -- Age clusters definition
    ages :: Map.Map Variable Int,  -- Map variables to age clusters (not the age itself)

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
    log_enabled = True,
    logfile = ["\x1b[1m" ++ ">> Log start <<" ++ "\x1b[0m"],

    bindings = Map.empty,

    variables = [],
    relations = [],
    clusters = Map.empty,
    ages = Map.empty,

    flag_id = 2,   -- Flag ids 0 and 1 are reserved, and represent the values 0 and 1
    type_id = 0,
      
    mappings = Map.empty
  }

-- ========================== --
-- ====== Log file ========== --

-- Enable or disable the logging -- The logging is initially enabled
enable_logs :: State ()
disable_logs :: State ()

-- If the log file is enabled, create a new log entry, if not, do nothing
new_log :: String -> State ()

-- Flush the log entries
print_logs :: State String
--------------------------
enable_logs =
  State (\ctx -> (ctx { log_enabled = True }, return ()))

disable_logs =
  State (\ctx -> (ctx { log_enabled = False }, return ()))

new_log p =
  State (\ctx -> if log_enabled ctx then
                   (ctx { logfile = p:(logfile ctx) }, return ())
                 else
                   (ctx, return ()))

print_logs =
  State (\ctx -> (ctx { logfile = [] }, return $ List.foldl (\s lg -> lg ++ "\n" ++ s) ("\x1b[1m" ++ ">> Log end <<" ++ "\x1b[0m") $ logfile ctx))

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


-- =============================== --
-- ========= Substitution ======== --

-- Insert a new mapping in the substitution
mapsto :: Variable -> Type -> State ()
-- Find the type a variable is mapped to
appmap :: Variable -> State Type
-- Output the list of mappings
mapping_list :: State [(Int, Type)]
-- Apply the mappings to a type
map_type_step :: Type -> State Type
map_type :: Type -> State Type   -- Caution : this function disregards the flag annotations when subs. (!n t) in (!m x)
-- Apply a valuation to a type
app_val :: Type -> Map.Map Flag Int -> State Type
-------------------------------------------------
mapsto x t = State (\ctx -> (ctx { mappings = Map.insert x t $ mappings ctx }, return ()))

appmap x = State (\ctx -> (ctx, case Map.lookup x $ mappings ctx of
                                  Just t -> return t
                                  _ -> return $ TVar x))

mapping_list =
  State (\ctx -> (ctx, return $ Map.assocs $ mappings ctx))

map_type_step (TVar x) = do
  appmap x

map_type_step (TArrow t u) = do
  t' <- map_type_step t
  u' <- map_type_step u
  return (TArrow t' u')

map_type_step (TTensor t u) = do
  t' <- map_type_step t
  u' <- map_type_step u
  return (TTensor t' u')

map_type_step (TExp n t) = do
  t' <- map_type_step t
  -- In this line : possible collision between the flag n and the flag of t' (if any)
  return (TExp n t')

map_type t = do
  t' <- map_type_step t
  if t == t' then
    return t
  else
    map_type t'

app_val (TExp n t) map = do
  t' <- app_val t map
  case Map.lookup n map of
    Just x -> do
        if x == 0 then do
          return t'
        else do
          return $ TExp 1 t'

    Nothing -> do
        return t'

app_val (TArrow t u) map = do
  t' <- app_val t map
  u' <- app_val u map
  return (TArrow t' u')

app_val (TTensor t u) map = do
  t' <- app_val t map
  u' <- app_val u map
  return (TTensor t' u')

app_val t _ = do
  return t


-------------------
-- Some printing --

instance Show Context where
  show ctx = "[| " ++ (Map.foldWithKey (\k t s -> s ++ subscript ("x" ++ show k) ++ " : " ++ pprint t ++ "\n") "" $ bindings ctx) 
 
