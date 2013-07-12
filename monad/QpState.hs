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

import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap
import Data.Map (Map)
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
--   The definition of the user types : recorded as a map from datacons to : the argument type, the data type it is part of
--   For the interpretation : an evaluation context including the current circuit and mappings

data Context = Ctx {

-- Log file  
  logfile :: Logfile,

-- File name and location in the file
  filename :: String,
  location :: Extent,  

-- Namespace, which contains the names of the term variables and datacons,
-- since those have been replaced by their unique id
  namespace :: Namespace,

-- Definition of the data constructors
-- The definition includes the name of the data type, and the expected type
-- This helps typing the constructor as :  datacon :: type -> usertype
  datacons :: IntMap (String, Type),

-- Information relevant to the flags
-- This includes the value of the flag, as well as the expression typed by
-- the type it is prefix of
  flags :: IntMap FlagInfo,


  gatesid :: Map String Int,

  circuits :: [Circuit],

    {- Id generation -}

    type_id :: Int, 
    flag_id :: Int,
    qbit_id :: Int,
     
    
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



-- | Definition of a state monad, with the associated state the above context
-- The monad runs its operations in the IO monad, so it can perform input / output operations
-- via a simple lift.
newtype QpState a = QpState { runS :: (Context -> IO (Context, a)) }

instance Monad QpState where
  return a = QpState { runS = (\ctx -> return (ctx, a)) }
  fail s = QpState { runS = (\ctx -> fail s) }
  st >>= action = QpState { runS = (\ctx -> do
                                    (ctx', a) <- runS st ctx 
                                    st' <- return $ action a
                                    runS st' ctx') }


-- | Throw an error
throwQ :: QError -> QpState a
throwQ e =
  QpState { runS = (\ctx -> E.throw e) }


-- | Catch any error thrown in a certain computation, running a continuation in case
-- an error has been caught
catchQ :: QpState a -> (QError -> QpState a) -> QpState a
catchQ st c =
  QpState { runS = (\ctx ->
                      (runS st ctx) `E.catch` (\e -> do
                                                 runS (c e) ctx)) }


-- | Relay actions from the IO monad to the QpState monad
liftIO :: IO a -> QpState a
liftIO x = QpState { runS = (\ctx -> do
                               x' <- x
                               return (ctx, x')) }



-- | The initial context, free of every thing, gates and others
empty_context :: Context
empty_context =  Ctx {
-- The logfile is initialized to print on the standard output, with the lowest verbose level possible
  logfile = Logfile { channel = stdin, verbose = 0 },

-- The namespace is initially empty
  namespace = N.new_namespace,

-- The initial location is unknown, as well as the name of the code file
  filename = "*UNKNOWN*",
  location = extent_unknown,

-- No predefined datacons or flags
  datacons = IMap.empty,
  flags = IMap.empty,
   
  gatesid = Map.empty,

  circuits = [],

  variables = [],
  relations = [],
  clusters = Map.empty,
  ages = Map.empty,

  flag_id = 2,   -- Flag ids 0 and 1 are reserved
  type_id = 0,
  qbit_id = 0,
      
  mappings = Map.empty
}



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


-- | Change the input file
set_file :: String -> QpState ()
set_file fname = do
  ctx <- get_context
  set_context $ ctx { filename = fname }


-- | Returns the current input file
get_file :: QpState String
get_file =
  get_context >>= return . filename




-- | Access to the name space : variable registration
register_var :: String -> QpState Int
register_var x = do
  ctx <- get_context
  (id, nspace) <- return $ N.register_var x (namespace ctx)
  set_context $ ctx { namespace = nspace }
  return id


-- | Access to the name space : variable registration
-- The datacon registration also records the type of the datacon in the field datacons
register_datacon :: String -> String -> Type -> QpState Int
register_datacon dcon typename dtype= do
  ctx <- get_context
  (id, nspace) <- return $ N.register_datacon dcon (namespace ctx)
  set_context $ ctx { namespace = nspace, datacons = IMap.insert id (typename, dtype) $ datacons ctx }
  return id


-- | Retrieves the definition of a datacon
datacon_def :: Int -> QpState (String, Type)
datacon_def id = do
  ctx <- get_context
  case IMap.lookup id $ datacons ctx of
    Just def ->
        return def
  
    Nothing ->
        -- The sound definition of the data constructors has already been checked
        -- during the translation into the core syntax
        throwQ $ ProgramError $ "Missing the definition of data constructor: " ++ subvar 'D' id




-- | Access to the information held by flags
-- Return the current value of a flag given by its reference
flag_value :: RefFlag -> QpState FlagValue
flag_value ref = do
  ctx <- get_context
  case IMap.lookup ref $ flags ctx of
    Just info ->
        return $ value info

    Nothing ->
        throwQ $ ProgramError $ "Undefined flag reference: " ++ subvar 'f' ref


-- | Access to the information held by a flag
-- Return the expresson, if any, typed by the associated type, and its location
referenced_expression :: RefFlag -> QpState (Maybe (TypeOf, Extent))
referenced_expression ref = do
  ctx <- get_context
  case IMap.lookup ref $ flags ctx of
    Just info -> do
        case (typeof info, elocation info) of
          (Just typof, Just loc) -> return $ Just (typof, loc)
          _ -> return $ Nothing

    Nothing ->
        -- One option would be to send an exception
        --    throwQ $ ProgramError $ "Undefined flag reference: " ++ subvar 'f' ref
        -- but he said flag can also be 0, 1 ... which are used as values, not referenced
        return $ Nothing


-- | Specify the expression typed by the associated type of an flag
specify_expression :: RefFlag -> TypeOf -> QpState ()
specify_expression ref typof = do
  ctx <- get_context
  set_context $ ctx { flags = IMap.update (\info -> Just $ info { typeof = Just typof }) ref $ flags ctx }


-- | Specify the expression typed by the associated type of an flag
specify_location :: RefFlag -> Extent -> QpState ()
specify_location ref loc = do
  ctx <- get_context
  set_context $ ctx { flags = IMap.update (\info -> Just $ info { elocation = Just loc }) ref $ flags ctx }


-- | Set the value of the flag to one
-- If the value previously recorded is incompatible with the new one, an error is generated (eg : old val = Zero)
set_flag :: RefFlag -> FlagValue -> QpState ()
set_flag ref v = do
  ctx <- get_context 
  case IMap.lookup ref $ flags ctx of
    Just info -> do
        case value info of
          Zero -> fail $ "Non duplicable expression"
          One -> return ()
          _ -> set_context $ ctx { flags = IMap.insert ref (info { value = One }) $ flags ctx }

    Nothing ->
        throwQ $ ProgramError $ "Undefined flag reference: " ++ subvar 'f' ref


-- | Generates a new flag reference, and add its accompying binding in the flags map
-- The flag is initially set to Unknown, with no expression or location
fresh_flag :: QpState RefFlag
fresh_flag = do
  ctx <- get_context
  id <- return $ flag_id ctx
  set_context $ ctx { flag_id = id + 1,
                      flags = IMap.insert id (FInfo { value = Unknown, typeof = Nothing, elocation = Nothing }) $ flags ctx }
  return id 


-- | Generates a new flag reference, and add its accompying binding in the flags map
-- The value of the new flag is set to the specified one, but it is still un-located
fresh_flag_with_value :: FlagValue -> QpState RefFlag
fresh_flag_with_value v = do
  ctx <- get_context
  id <- return $ flag_id ctx
  set_context $ ctx { flag_id = id + 1,
                      flags = IMap.insert id (FInfo { value = v, typeof = Nothing, elocation = Nothing }) $ flags ctx }
  return id 




-- | Retrieves the id of a gate
gate_id :: String -> QpState Int
gate_id g = do
  ctx <- get_context
  case Map.lookup g $ gatesid ctx of
    Just id ->
        return id
 
    Nothing ->
        fail "Unregistered gate"


{-
  Id generation
    - fresh_var/type/flag return a fresh id of the corresponding kind
    - new_type creates a new type !n a where n and a are fresh
    - create_pattern_type creates a type matching the structure of the pattern
-}

fresh_type :: QpState Variable

new_type :: QpState Type
----------------------------------------------------------------
fresh_type = QpState (\ctx -> return (ctx { type_id = (+1) $ type_id ctx }, type_id ctx))

new_type = do
  x <- fresh_type
  f <- fresh_flag
  return (TBang f (TVar x))


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
app_val_to_flag :: RefFlag -> Map.Map Int Int -> QpState RefFlag
app_val_to_lintype :: LinType -> Map.Map Int Int -> QpState LinType
app_val_to_type :: Type -> Map.Map Int Int -> QpState Type
-------------------------------------------------
mapsto x t = QpState (\ctx -> return (ctx { mappings = Map.insert x t $ mappings ctx }, ()))

appmap x = QpState (\ctx -> return (ctx, case Map.lookup x $ mappings ctx of
                                         Just t -> t
                                         _ -> TVar x))

mapping_list =
  QpState (\ctx -> return (ctx, Map.assocs $ mappings ctx))

map_lintype_step TUnit = do
  return TUnit

map_lintype_step TBool = do
  return TBool

map_lintype_step TQbit = do
  return TQbit

map_lintype_step (TVar x) = do
  t <- appmap x
  case t of
    (TVar y) | y == x -> return (TVar x)
             | otherwise -> return t
    _ -> return t

map_lintype_step (TArrow t u) = do
  t' <- map_type_step t
  u' <- map_type_step u
  return (TArrow t' u')

map_lintype_step (TTensor tlist) = do
  tlist' <- List.foldr (\t rec -> do
                          r <- rec
                          t' <- map_type_step t
                          return (t':r)) (return []) tlist
  return (TTensor tlist')

map_lintype_step (TCirc t u) = do
  t' <- map_type_step t
  u' <- map_type_step u
  return (TCirc t' u')

map_type_step (TBang f t) = do
  t' <- map_lintype_step t
  return $ TBang f t'

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
  return (TVar x)

app_val_to_lintype (TArrow t u) map = do
  t' <- app_val_to_type t map
  u' <- app_val_to_type u map
  return (TArrow t' u')

app_val_to_lintype (TTensor tlist) map = do
  tlist' <- List.foldr (\t rec -> do
                          r <- rec
                          t' <- app_val_to_type t map
                          return (t':r)) (return []) tlist
  return (TTensor tlist')

app_val_to_lintype (TCirc t u) map = do
  t' <- app_val_to_type t map
  u' <- app_val_to_type u map
  return (TCirc t' u')

app_val_to_type (TBang f t) map = do
  fv <- app_val_to_flag f map
  t' <- app_val_to_lintype t map
  return $ TBang fv t' 
