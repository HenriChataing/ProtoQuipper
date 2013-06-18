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
-- Context definition  --

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

 --   type_ann :: Map.Map Int Type, -- Records the mappings flag <-> type,  eg in !nT, n points to T

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
    mappings :: Map.Map Variable LinType
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


-- Fail with a specific error message
failwith :: Error -> State a
-----------------------------
failwith err =
  State (\ctx -> (ctx, error_fail err)) 

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

import_gates :: [(Variable, Type)] -> State ()
----------------------------------------------
import_gates l = do
  List.foldl (\rec (x, t) -> do
                rec
                bind_var x t) (return ()) l

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
--------------------------------

fresh_type = State (\ctx -> (ctx { type_id = (+1) $ type_id ctx }, Ok $ type_id ctx))
fresh_flag = State (\ctx -> (ctx { flag_id = (+1) $ flag_id ctx }, Ok $ flag_id ctx))

ntypes = State (\ctx -> (ctx, Ok $ type_id ctx))

new_type = do
  x <- fresh_type
  f <- fresh_flag
  return (TExp f $ TVar x)

-- =========================== --
-- === Context annotations === --

-- Return the flag annotation of the context, as a list of associations (term * flag)
context_annotation :: State [(Variable, Flag)]
----------------------------------------------
context_annotation = State (\ctx -> (ctx, Ok $  Map.foldWithKey (\x (TExp f _) ann -> (x, f):ann)
                                                                [] $ bindings ctx))

-- ============================ --
-- === Context manipulation === --

-- Add a new bindings (var * type) in the current typing context
bind_var :: Variable -> Type -> State ()
-- Create types for each of the variables of the pattern, bind those variables in the context, and return the resulting type
bind_pattern :: Pattern -> State Type
bind_pattern_with_type :: Pattern -> Type -> State ()
create_pattern_type :: Pattern -> State (Type, [FlagConstraint])
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

bind_pattern PUnit = do
  return $ TExp (-1) TUnit

bind_pattern (PVar x) = do
  a <- new_type
  bind_var x a
  return a

bind_pattern (PPair p q) = do
  t@(TExp f _) <- bind_pattern p
  u@(TExp g _) <- bind_pattern q
  n <- fresh_flag
  return $ TExp n (TTensor t u)

bind_pattern_with_type PUnit (TExp _ TUnit) = do
  return ()

bind_pattern_with_type (PVar x) t = do
  bind_var x t

bind_pattern_with_type (PPair p q) (TExp _ (TTensor t u)) = do
  bind_pattern_with_type p t
  bind_pattern_with_type q u

bind_pattern_with_type _ _ = do
  fail "Unmatching pair of pattern / type"

create_pattern_type PUnit = do
  return (TExp (-1) TUnit, [])

create_pattern_type (PVar _) = do
  t <- new_type
  return (t, [])

create_pattern_type (PPair p q) = do
  (t@(TExp f _), fct) <- create_pattern_type p
  (u@(TExp g _), fcu) <- create_pattern_type q
  n <- fresh_flag
  return (TExp n (TTensor t u), (n, f):(n, g):(fct ++ fcu))

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
mapsto :: Variable -> LinType -> State ()
-- Find the type a variable is mapped to
appmap :: Variable -> State LinType
-- Output the list of mappings
mapping_list :: State [(Int, LinType)]
-- Apply the mappings to a type
map_type_step :: Type -> State Type
map_lintype_step :: LinType -> State LinType
map_type :: Type -> State Type
-- Apply a valuation to a type
app_val_to_flag :: Flag -> Map.Map Int Int -> State Flag
app_val_to_lintype :: LinType -> Map.Map Int Int -> State LinType
app_val_to_type :: Type -> Map.Map Int Int -> State Type
-------------------------------------------------
mapsto x t = State (\ctx -> (ctx { mappings = Map.insert x t $ mappings ctx }, return ()))

appmap x = State (\ctx -> (ctx, case Map.lookup x $ mappings ctx of
                                  Just t -> return t
                                  _ -> return $ TVar x))

mapping_list =
  State (\ctx -> (ctx, return $ Map.assocs $ mappings ctx))

map_lintype_step TUnit = do
  return TUnit

map_lintype_step TBool = do
  return TBool

map_lintype_step TQbit = do
  return TQbit

map_lintype_step (TVar x) = do
  t <- appmap x
  return t

map_lintype_step (TArrow t u) = do
  t' <- map_type_step t
  u' <- map_type_step u
  return $ TArrow t' u'

map_lintype_step (TTensor t u) = do
  t' <- map_type_step t
  u' <- map_type_step u
  return $ TTensor t' u'

map_lintype_step (TCirc t u) = do
  t' <- map_type_step t
  u' <- map_type_step u
  return $ TCirc t' u'

map_type_step (TExp f t) = do
  t' <- map_lintype_step t
  return $ TExp f t'

map_type t = do
  t' <- map_type_step t
  if t == t' then
    return t
  else
    map_type t'

app_val_to_flag n map = do
  if n < 2 then
    return n
  else do
    case Map.lookup n map of
      Just x -> do
          return x

      Nothing -> do
          return n

app_val_to_lintype TUnit _ = do
  return TUnit

app_val_to_lintype TBool _ = do
  return TBool

app_val_to_lintype TQbit _ = do
  return TQbit

app_val_to_lintype (TVar x) _ = do
  return $ TVar x

app_val_to_lintype (TArrow t u) map = do
  t' <- app_val_to_type t map
  u' <- app_val_to_type u map
  return $ TArrow t' u'

app_val_to_lintype (TTensor t u) map = do
  t' <- app_val_to_type t map
  u' <- app_val_to_type u map
  return $ TTensor t' u'

app_val_to_lintype (TCirc t u) map = do
  t' <- app_val_to_type t map
  u' <- app_val_to_type u map
  return $ TCirc t' u'

app_val_to_type (TExp f t) map = do
  fv <- app_val_to_flag f map
  t' <- app_val_to_lintype t map
  return $ TExp fv t'


-------------------
-- Some printing --

instance Show Context where
  show ctx = "[| " ++ (Map.foldWithKey (\k t s -> s ++ subscript ("x" ++ show k) ++ " : " ++ pprint t ++ "\n") "" $ bindings ctx) 
 
