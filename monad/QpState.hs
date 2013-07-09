module QpState where

import Localizing (Extent, extent_unknown)
import Utils
import QuipperError

import Namespace (Namespace)
import qualified Namespace as N

import CoreSyntax
import Circuits
import Subtyping

import System.IO

import Control.Exception as E

import LayeredMap (LayeredMap)
import qualified LayeredMap as LMap
import qualified Data.Map as Map
import Data.List as List
import Data.Array as Array
import qualified Data.Set as Set
import Data.Sequence as Seq 

-- | Implementation of a logger. Logs can be given different priorities, depending on their importance.
-- The verbose control then discards any log whose priority is lower than the control. The logs are printed
-- to a channel, which can be, for example, stdout, stderr, any file writing channel

data Logfile = Logfile {
  channel :: Handle,
  verbose :: Int
}

-- | Enter a log with a given priority level
write_log :: Logfile -> Int -> String -> IO ()
write_log logfile lvl s = do
  w <- hIsWritable $ channel logfile
  if lvl < verbose logfile || not w  then
    return ()
  else
    hPutStrLn (channel logfile) s

-- | Definition of the context in which all quipper functions are evluated. This means this context is used
-- from parsing to interpretation and type inference. Using a single context has been preferred over using
-- several specific to each module to avoid having to convey information between states. 
-- This also means all the data structures necessary to each module have to be included in the context, which now
-- contains :
--   A logfile, used for regular and debug printing
--   Information relevant to the original expression (location in file, sample of the current expression)
--   A namespace to record the variables of the original expression
--   For the interpretation : an evaluation context including the current circuit and mappings

data Context = Ctx {
  
  logfile :: Logfile,
  location :: Extent,
  namespace :: Namespace,
   
  circuits :: [Circuit],

    {- Id generation -}

    type_id :: Int, 
    flag_id :: Int,
    var_id :: Int,
    qbit_id :: Int,

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

newtype QpState a = QpState { runS :: (Context -> IO (Context, a)) }

instance Monad QpState where
  return a = QpState { runS = (\ctx -> return (ctx, a)) }
  fail s = QpState { runS = (\ctx -> fail s) }
  st >>= action = QpState { runS = (\ctx -> do
                                    (ctx', a) <- runS st ctx 
                                    st' <- return $ action a
                                    runS st' ctx') }

throwQ :: QError -> QpState a
throwQ e =
  QpState { runS = (\ctx -> E.throw e) }

catchQ :: QpState a -> (QError -> QpState a) -> QpState a
catchQ st c =
  QpState { runS = (\ctx ->
                      (runS st ctx) `E.catch` (\e -> do
                                                 runS (c e) ctx)) }

-- Create an empty context (without the basic gates)
empty_context :: Context
------------------------
empty_context =
  Ctx {
    logfile = Logfile { channel = stdin, verbose = 0 },
    namespace = N.new_namespace,
    location = extent_unknown,

    circuits = [],

    name_to_var = [Map.empty],
    var_to_name = Map.empty,

    variables = [],
    relations = [],
    clusters = Map.empty,
    ages = Map.empty,

    flag_id = 2,   -- Flag ids 0 and 1 are reserved
    type_id = 0,
    var_id = 0,
    qbit_id = 0,
      
    mappings = Map.empty
  }


-- | Relay actions from the IO monad to the QpState monad
liftIO :: IO a -> QpState a
liftIO x = QpState { runS = (\ctx -> do
                               x' <- x
                               return (ctx, x')) }


-- | Returns the state context
get_context :: QpState Context
get_context = QpState { runS = (\ctx -> return (ctx, ctx)) }


-- | Set the state context
set_context :: Context -> QpState ()
set_context ctx = QpState { runS = (\_ -> return (ctx, ())) }


-- | Enter a new log entry
newlog :: Int -> String -> QpState ()
newlog lvl entry = do
  ctx <- get_context
  liftIO $ write_log (logfile ctx) lvl entry


-- | Flush the log file, and the concatenation of the logs previously in
-- the log file
flush_logs :: QpState ()
flush_logs = do
  ctx <- get_context
  liftIO $ hFlush (channel $ logfile ctx)


-- | The set location marker
set_location :: Extent -> QpState ()
set_location ex = do
  ctx <- get_context
  set_context $ ctx { location = ex }


-- | Return the current location marker
get_location :: QpState Extent
get_location =
  get_context >>= return . location


{-
  Id generation
    - fresh_var/type/flag return a fresh id of the corresponding kind
    - new_type creates a new type !n a where n and a are fresh
    - create_pattern_type creates a type matching the structure of the pattern
-}

fresh_type :: QpState Variable
fresh_flag :: QpState Flag
fresh_var :: QpState Variable
new_type :: QpState Type
create_pattern_type :: Pattern -> QpState (Type, [FlagConstraint])
----------------------------------------------------------------
fresh_type = QpState (\ctx -> return (ctx { type_id = (+1) $ type_id ctx }, type_id ctx))

fresh_flag = QpState (\ctx -> return (ctx { flag_id = (+1) $ flag_id ctx }, flag_id ctx))

fresh_var = QpState (\ctx -> return (ctx { var_id = (+1) $ var_id ctx }, var_id ctx))

new_type = do
  x <- fresh_type
  f <- fresh_flag
  return (TExp f (TVar x, NoInfo))

create_pattern_type (PLocated p ex) = do
  set_location ex
  create_pattern_type p

create_pattern_type PUnit = do
  ex <- get_location
  detail <- return $ ActualOfP PUnit ex
  return (TExp (-1) (TUnit, detail), [])

create_pattern_type (PVar x) = do
  t <- fresh_type
  n <- fresh_flag
  
  ex <- get_location
  detail <- return $ ActualOfP (PVar x) ex
  return (TExp n (TVar t, detail), [])

create_pattern_type (PPair p q) = do
  ex <- get_location

  (t@(TExp f _), fct) <- create_pattern_type p
  (u@(TExp g _), fcu) <- create_pattern_type q
  n <- fresh_flag
  
  detail <- return $ ActualOfP (PPair p q) ex
  return (TExp n (TTensor t u, detail), (n, f):(n, g):(fct ++ fcu))


-- =============================== --
-- ========= Substitution ======== --

-- Insert a new mapping in the substitution
mapsto :: Variable -> LinType -> QpState ()
-- Find the type a variable is mapped to
appmap :: Variable -> QpState LinType
-- Output the list of mappings
mapping_list :: QpState [(Int, LinType)]
-- Apply the mappings to a type
map_type_step :: Type -> QpState Type
map_lintype_step :: LinType -> QpState LinType
map_type :: Type -> QpState Type
-- Apply a valuation to a type
app_val_to_flag :: Flag -> Map.Map Int Int -> QpState Flag
app_val_to_lintype :: LinType -> Map.Map Int Int -> QpState LinType
app_val_to_type :: Type -> Map.Map Int Int -> QpState Type
-------------------------------------------------
mapsto x t = QpState (\ctx -> return (ctx { mappings = Map.insert x t $ mappings ctx }, ()))

appmap x = QpState (\ctx -> return (ctx, case Map.lookup x $ mappings ctx of
                                         Just t -> t
                                         _ -> (TVar x, NoInfo)))

mapping_list =
  QpState (\ctx -> return (ctx, Map.assocs $ mappings ctx))

map_lintype_step (TUnit, d) = do
  return (TUnit, d)

map_lintype_step (TBool, d) = do
  return (TBool, d)

map_lintype_step (TQbit, d) = do
  return (TQbit, d)

map_lintype_step (TVar x, d) = do
  t <- appmap x
  case t of
    (TVar y, _) | y == x -> return (TVar x, d)
                | otherwise -> return t
    _ -> return t

map_lintype_step (TArrow t u, d) = do
  t' <- map_type_step t
  u' <- map_type_step u
  return (TArrow t' u', d)

map_lintype_step (TTensor t u, d) = do
  t' <- map_type_step t
  u' <- map_type_step u
  return (TTensor t' u', d)

map_lintype_step (TSum t u, d) = do
  t' <- map_type_step t
  u' <- map_type_step u
  return (TSum t' u', d)

map_lintype_step (TCirc t u, d) = do
  t' <- map_type_step t
  u' <- map_type_step u
  return (TCirc t' u', d)

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

app_val_to_lintype (TUnit, d) _ = do
  return (TUnit, d)

app_val_to_lintype (TBool, d) _ = do
  return (TBool, d)

app_val_to_lintype (TQbit, d) _ = do
  return (TQbit, d)

app_val_to_lintype (TVar x, d) _ = do
  return (TVar x, d)

app_val_to_lintype (TArrow t u, d) map = do
  t' <- app_val_to_type t map
  u' <- app_val_to_type u map
  return (TArrow t' u', d)

app_val_to_lintype (TTensor t u, d) map = do
  t' <- app_val_to_type t map
  u' <- app_val_to_type u map
  return (TTensor t' u', d)

app_val_to_lintype (TSum t u, d) map = do
  t' <- app_val_to_type t map
  u' <- app_val_to_type u map
  return (TSum t' u', d)

app_val_to_lintype (TCirc t u, d) map = do
  t' <- app_val_to_type t map
  u' <- app_val_to_type u map
  return (TCirc t' u', d)

app_val_to_type (TExp f t) map = do
  fv <- app_val_to_flag f map
  t' <- app_val_to_lintype t map
  return $ TExp fv t' 
