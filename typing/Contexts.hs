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

{-
  Definition of the context
  A same context is used for all the steps of the type inference algorithm (to avoid having to convey in information
  from one to another).

  The specification of the context is

  - logs : a small logging system is added to have in place printing (for debugging purposes)
    This include a logfile (each log takes a line), and a boolean flag to enable/disable logging
    (in which case the logs are not saved)

  - translation of programs : the programs have to be translated to the core syntax (few differences)
    Variables are labelled with a unique id at this moment, and type variables the same

  - 
-}

data Context =
  Ctx {

    {- Log file, logging and debugging -}

    log_enabled :: Bool,
    logfile :: [String],

    current_location :: Extent,
    current_expr :: Expr,

    {- Id generation -}

    type_id :: Int, 
    flag_id :: Int,
    var_id :: Int,

    {-
       Translation to core syntax :

       - name_to_var remembers the bindings from the variable names to the given variable id
         It is organized in layers, each corresponding to a scope in the context
         Eg : in let p = e in f, the variables of p are registered in a new layer in the context of f
         One can not simply erase the name from the context since one name can be used multiple times in the same context

       - var_to_name remembers the name of the variable an id points to

       - var location is the location of the variable declaration
    -}
     
    name_to_var :: [Map.Map String Variable],
    var_to_name :: Map.Map Variable String,
    
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

{- Monad instance declaration of the above context -}

newtype State a = State (Context -> (Context, Computed a))

instance Monad State where
  return a = State (\ctx -> (ctx, Ok a))
  fail s = State (\ctx -> (ctx, Failed $ CustomError s extent_unknown))
  State run >>= action = State (\ctx -> let (ctx', a) = run ctx in
                                        case a of
                                          Ok a -> let State run' = action a in
                                                  run' ctx'
                                          Failed err -> (ctx', Failed err))

-- Additional state function : fail with a specific error message
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
    current_location = extent_unknown,
    current_expr = EUnit,

    name_to_var = [Map.empty],
    var_to_name = Map.empty,

    variables = [],
    relations = [],
    clusters = Map.empty,
    ages = Map.empty,

    flag_id = 2,   -- Flag ids 0 and 1 are reserved
    type_id = 0,
    var_id = 0,
      
    mappings = Map.empty
  }

{- 
  Log file and logging. The function provided are :
 
  - enable/disable_logs : do as the name indicates
  - new_log : enter a new log in the log file
  - print_logs : returns the logs contained in the file, and empty the log file

  - set_location / get_location : do as their name indicates
-}
  
enable_logs :: State ()
disable_logs :: State ()
new_log :: String -> State ()
print_logs :: State String

set_location :: Extent -> State ()
get_location :: State Extent
set_expr :: Expr -> State ()
get_expr :: State Expr
----------------------------
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

set_location ex =
  State (\ctx -> (ctx { current_location = ex }, return ()))

get_location =
  State (\ctx -> (ctx, return $ current_location ctx))

set_expr e =
  State (\ctx -> (ctx { current_expr = e }, return ()))

get_expr =
  State (\ctx -> (ctx, return $ current_expr ctx))

{-
  Id generation
    - fresh_var/type/flag return a fresh id of the corresponding kind
    - new_type creates a new type !n a where n and a are fresh
    - create_pattern_type creates a type matching the structure of the pattern
-}

fresh_type :: State Variable
fresh_flag :: State Flag
fresh_var :: State Variable
new_type :: State Type
create_pattern_type :: Pattern -> State (Type, [FlagConstraint])
----------------------------------------------------------------
fresh_type = State (\ctx -> (ctx { type_id = (+1) $ type_id ctx }, Ok $ type_id ctx))

fresh_flag = State (\ctx -> (ctx { flag_id = (+1) $ flag_id ctx }, Ok $ flag_id ctx))

fresh_var = State (\ctx -> (ctx { var_id = (+1) $ var_id ctx }, Ok $ var_id ctx))

new_type = do
  x <- fresh_type
  f <- fresh_flag
  return (TExp f $ TVar x)

create_pattern_type PUnit = do
  return (TExp (-1) TUnit, [])

create_pattern_type (PVar x) = do
  t <- fresh_type
  n <- fresh_flag
  dett <- return $ TExp n $ TDetailed (TVar t) (TypeOfP $ PVar x)
  return (dett, [])

create_pattern_type (PPair p q) = do
  (t@(TExp f _), fct) <- create_pattern_type p
  (u@(TExp g _), fcu) <- create_pattern_type q
  n <- fresh_flag
  return (TExp n $ TDetailed (TTensor t u) (TypeOfP $ PPair p q), (n, f):(n, g):(fct ++ fcu))


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

map_lintype_step (TDetailed t det) = do
  t' <- map_lintype_step t
  return $ TDetailed t' det

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

app_val_to_lintype (TDetailed t det) map = do
  t' <- app_val_to_lintype t map
  return $ TDetailed t' det

app_val_to_type (TExp f t) map = do
  fv <- app_val_to_flag f map
  t' <- app_val_to_lintype t map
  return $ TExp fv t' 
