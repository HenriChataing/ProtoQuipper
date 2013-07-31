module Monad.QpState where

import Utils
import Classes
import Builtins

import Parsing.Localizing (Extent, extent_unknown)

import Monad.Modules
import Monad.QuipperError
import Monad.Namespace (Namespace)
import qualified Monad.Namespace as N

import Typing.CoreSyntax
import Typing.CorePrinter

import Interpret.Circuits
import Interpret.Values

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
  if lvl >= verbose logfile || not w then
    return ()
  else do
    hPutStrLn (channel logfile) s
    hFlush (channel logfile)



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


-- All stuff to support module imports
  -- List of processed modules
  modules :: [(String, Module)],
  -- Current module
  cmodule :: Module,
 
  -- Global variables (imported from other modules)
  globals :: IntMap Type, 


-- Builtin values
  builtins :: Map String (Type, Value),

-- Namespace, which contains the names of the term variables and datacons,
-- since those have been replaced by their unique id
  namespace :: Namespace,

-- Definition of the types
-- Types are referenced by their name. Is recorded the number of type arguments
-- needed by any type
  types :: Map String Typespec,

-- Definition of the data constructors
-- The definition includes the name of the data type, and the expected type
-- This helps typing the constructor as :  datacon :: type -> usertype
--                                   or :  datacon :: usertype
-- depending on whether the constructor takes an argument or not
  datacons :: IntMap Type,

-- Information relevant to the flags
-- This includes the value of the flag, as well as the expression typed by
-- the type it is prefix of
  flags :: IntMap FlagInfo,

-- Circuit stack
  circuits :: [Circuit],

-- Id generation
  type_id :: Int, 
  flag_id :: Int,
  qbit_id :: Int,
     
-- Variable ordering
-- Variables are grouped into clusters of variables sharing the same age    
  relations :: [(Int, Int)],
  clusters :: IntMap [Type],  -- Age clusters definition
  cmap :: IntMap Int,  -- Map variables to age clusters


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
  logfile = Logfile { channel = stdout, verbose = 0 },

-- The namespace is initially empty
  namespace = N.new_namespace,

-- No modules
  modules = [],
-- Current module is dummy
  cmodule = dummy_module,
 
-- No global variables
  globals = IMap.empty, 


-- No builtins, added later
  builtins = Map.empty,

-- The initial location is unknown, as well as the name of the code file
  filename = "*UNKNOWN*",
  location = extent_unknown,

-- No predefined types, datacons or flags
  types = Map.empty,
  datacons = IMap.empty,
  flags = IMap.empty,

  circuits = [],

  relations = [],
  clusters = IMap.empty,
  cmap = IMap.empty,

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



-- | Change the level of verbosity
set_verbose :: Int -> QpState ()
set_verbose v = do
  ctx <- get_context
  set_context $ ctx { logfile = (logfile ctx) { verbose = v } }


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


get_module :: QpState Module
get_module =
  get_context >>= return . cmodule


-- | Access to the name space : variable registration
register_var :: String -> QpState Int
register_var x = do
  ctx <- get_context
  (id, nspace) <- return $ N.register_var x (namespace ctx)
  set_context $ ctx { namespace = nspace }
  return id


-- | Create a dummy variable from a new id n, registered under the name x_n
dummy_var :: QpState Int
dummy_var = do
  ctx <- get_context
  (id, nspace) <- return $ N.dummy_var (namespace ctx)
  set_context $ ctx { namespace = nspace }
  return id


-- | Access to the name space : variable registration
-- The datacon registration also records the type of the datacon in the field datacons
register_datacon :: String -> Type -> QpState Int
register_datacon dcon dtype = do
  ctx <- get_context
  (id, nspace) <- return $ N.register_datacon dcon (namespace ctx)
  set_context $ ctx { namespace = nspace, datacons = IMap.insert id dtype $ datacons ctx }
  return id


-- | resgister the definition of a type
register_type :: String -> Typespec -> QpState ()
register_type typ spec = do
  ctx <- get_context
  set_context $ ctx { types = Map.insert typ spec $ types ctx }


-- | Return the name of the variable 
-- Looks in the namespace for the name of the variable n. If no match is found,
-- a standard name x_n is produced
variable_name :: Variable -> QpState String
variable_name x = do
  ctx <- get_context
  case IMap.lookup x $ N.varcons (namespace ctx) of
    Just n ->
        return n

    Nothing ->
        return $ subvar 'x' x


-- | Return the name of the datacon
-- Looks in the namespace for the name of the datacon d. If no match is found,
-- a standard name D_n is produced
datacon_name :: Variable -> QpState String
datacon_name x = do
  ctx <- get_context
  case IMap.lookup x $ N.datacons (namespace ctx) of
    Just n ->
        return n

    Nothing ->
        return $ subvar 'D' x



-- | Request for the variable x to be exported (added to the current module export list)
export_var :: Variable -> QpState ()
export_var x = do
  ctx <- get_context
  -- Current module
  cm <- return $ cmodule ctx
  -- Name of the variable
  name <- variable_name x

  set_context $ ctx { cmodule = cm { global_ids = Map.insert name x $ global_ids cm,
                                     global_types = IMap.insert x (TBang (-1) TUnit) $ global_types cm,
                                     global_vars = IMap.insert x VUnit $ global_vars cm } }


-- | Import the global variables and types from the module dependencies in the globals field
import_globals :: QpState ()
import_globals = do
  ctx <- get_context
  cm <- get_module
  (gvs, gts) <- List.foldl (\rec m -> do
                              (gv, gt) <- rec
                              -- Look for the definition of the module m
                              case List.lookup m $ modules ctx of
                                Just mod -> do
                                    return $ (IMap.union gv (global_types mod), Map.union gt (typespecs mod))

                                Nothing ->
                                    throwQ $ ProgramError $ "missing module implementation of " ++ m) (return (IMap.empty, Map.empty)) $ dependencies cm
  set_context $ ctx { globals = gvs, types = gts }


-- | Lookup the type of a global variable
type_of_global :: Variable -> QpState Type
type_of_global x = do
  ctx <- get_context
  case IMap.lookup x $ globals ctx of
    Just t ->
        return t
    Nothing -> do
        n <- variable_name x
        throwQ $ ProgramError $ "undefined global variable " ++ n


-- | Look up variable in a specific module (typically used with a qualified variable)
lookup_qualified_var :: (String, String) -> QpState Variable
lookup_qualified_var (mod, n) = do
  ctx <- get_context
  -- Check that the module is part of the dependencies
  if List.elem mod $ dependencies (cmodule ctx) then do
    case List.lookup mod $ modules ctx of
      Just modi -> do
          case Map.lookup n $ global_ids modi of
            Just x -> return x
            Nothing -> do
                ex <- get_location
                f <- return $ codefile (cmodule ctx)
                throwQ $ UnboundVariable (mod ++ "." ++ n) (f, ex)

      Nothing -> do
          ex <- get_location
          f <- return $ codefile (cmodule ctx)
          throwQ $ UnboundVariable (mod ++ "." ++ n) (f, ex)

  else do
    ex <- get_location
    f <- return $ codefile (cmodule ctx)
    throwQ $ UnboundVariable (mod ++ "." ++ n) (f, ex)


-- | Look up a type from a specific module (typically used with a qualified variable)
lookup_qualified_type :: (String, String) -> QpState Typespec
lookup_qualified_type (mod, n) = do
  ctx <- get_context
  -- Check that the module is part of the dependencies
  if List.elem mod $ dependencies (cmodule ctx) then do
    case List.lookup mod $ modules ctx of
      Just modi -> do
          case Map.lookup n $ typespecs modi of
            Just x -> return x
            Nothing -> do
                ex <- get_location
                f <- return $ codefile (cmodule ctx)
                throwQ $ UnboundVariable (mod ++ "." ++ n) (f, ex)

      Nothing -> do
          ex <- get_location
          f <- return $ codefile (cmodule ctx)
          throwQ $ UnboundVariable (mod ++ "." ++ n) (f, ex)

  else do
    ex <- get_location
    f <- return $ codefile (cmodule ctx)
    throwQ $ UnboundVariable (mod ++ "." ++ n) (f, ex)


-- | Lookup for the type of a builtin
builtin_type :: String -> QpState Type
builtin_type s = do
  ctx <- get_context
  case Map.lookup s $ builtins ctx of
    Just (t, _) ->
        return t
    Nothing ->
        throwQ $ ProgramError $ "Missing builtin: " ++ s


-- | Lookup for the value of a builtin
builtin_value :: String -> QpState Value
builtin_value s = do
  ctx <- get_context
  case Map.lookup s $ builtins ctx of
    Just (_, v) ->
        return v
    Nothing ->
        throwQ $ ProgramError $ "Missing builtin: " ++ s



-- | Check the state for a type name
exist_type :: String -> QpState Bool
exist_type typename = do
  ctx <- get_context
  return $ Map.member typename $ types ctx


-- | Create the initializer of the translation into internal syntax : create a namescape including
-- all the global variables from the module dependencies. 
global_namespace :: QpState (Map String Variable)
global_namespace = do
  ctx <- get_context
  cmod <- get_module
  List.foldl (\rec m -> do
                nsp <- rec
                case List.lookup m $ modules ctx of
                  Just m ->
                      return $ Map.union (global_ids m) nsp

                  Nothing ->
                      throwQ $ ProgramError $ "missing implementation of module " ++ m) (return Map.empty) $ dependencies cmod



-- | Create the initializer of the interpretation : create an evaluation context including
-- all the global variables from the module dependencies
global_context :: QpState (IntMap Value)
global_context = do
  ctx <- get_context
  cmod <- get_module
  List.foldl (\rec m -> do
                ectx <- rec
                case List.lookup m $ modules ctx of
                  Just m ->
                      return $ IMap.union (global_vars m) ectx

                  Nothing ->
                      throwQ $ ProgramError $ "missing implementation of module " ++ m) (return IMap.empty) $ dependencies cmod



-- | Retrieves the definition of a type
type_spec :: String -> QpState Typespec
type_spec typ = do
  ctx <- get_context
  case Map.lookup typ $ types ctx of
    Just n ->
        return n

    Nothing ->
        throwQ $ ProgramError $ "Missing the definition of the type: " ++ typ


-- | Retrieves the definition of a datacon
datacon_def :: Int -> QpState Type
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
flag_value ref =
  case ref of
    (-1) -> return Any
    0 -> return Zero
    1 -> return One
    _ -> do
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
set_flag :: RefFlag-> QpState ()
set_flag ref = do
  case ref of
    (-1) -> return ()
    0 -> do
        f <- get_file
        throwQ $ NonDuplicableError "(unknown)" (f, extent_unknown)
    1 -> return ()
    _ -> do
        ctx <- get_context 
        case IMap.lookup ref $ flags ctx of
          Just info -> do
              case value info of
                Zero -> do
                    throw_NonDuplicableError ref
                One ->
                    return ()
                _ ->
                    set_context $ ctx { flags = IMap.insert ref (info { value = One }) $ flags ctx }

          Nothing ->
              throwQ $ ProgramError $ "Undefined flag reference: " ++ subvar 'f' ref


-- | Set the value of the flag to zero
-- If the value previously recorded is incompatible with the new one, an error is generated (eg : old val = One)
unset_flag :: RefFlag -> QpState ()
unset_flag ref = do
  case ref of
    (-1) -> return ()
    0 -> return ()
    1 -> do
        f <- get_file
        throwQ $ NonDuplicableError "(unknown)" (f, extent_unknown)
    _ -> do
        ctx <- get_context 
        case IMap.lookup ref $ flags ctx of
          Just info -> do
              case value info of
                One ->
                    throw_NonDuplicableError ref
                Zero ->
                    return ()
                _ ->
                    set_context $ ctx { flags = IMap.insert ref (info { value = Zero }) $ flags ctx }

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


-- | Create a new flag reference, initialized with the information
-- referenced by the argument flag
duplicate_flag :: RefFlag -> QpState RefFlag
duplicate_flag ref = do
  case ref of
    (-1) -> return (-1)
    0 -> return 0
    1 -> return 1
    _ -> do
        ctx <- get_context
        id <- return $ flag_id ctx
        case IMap.lookup ref $ flags ctx of
          Just info -> do
              set_context $ ctx { flag_id = id + 1,
                                  flags = IMap.insert id info $ flags ctx }
              return id

          Nothing ->
              throwQ $ ProgramError $ "Undefined flag reference: " ++ subvar 'f' ref

-- | Generic type instanciation
-- New variables are produced for every generalized over, and substitute the old ones in the type and the constraints
instanciate_scheme :: [RefFlag] -> [Variable] -> ConstraintSet -> Type -> QpState (Type, ConstraintSet)
instanciate_scheme refs vars cset typ = do
  -- Replace the flag references by new ones
  (typ', cset') <- List.foldl (\rec ref -> do
                                 (typ, cset) <- rec
                                 nref <- duplicate_flag ref
                                 typ' <- return $ subs_flag ref nref typ
                                 cset' <- return $ subs_flag ref nref cset
                                 return (typ', cset')) (return (typ, cset)) refs

  -- Replace the variables
  List.foldl (\rec var -> do
                (typ, cset) <- rec
                nvar <- fresh_type
                typ' <- return $ subs_typ_var var (TVar nvar) typ
                cset' <- return $ subs_typ_var var (TVar nvar) cset
                return (typ', cset')) (return (typ', cset')) vars


-- | If the type is generic, then it instanciates the typing scheme, else it just returns the type
instanciate :: Type -> QpState (Type, ConstraintSet)
instanciate (TForall refs vars cset typ) =
  instanciate_scheme refs vars cset typ

instanciate typ =
  return (typ, emptyset)


-- | Replaces all the flag references by their actual value :
--     0 if no flag
--     1 of one
--     -1 of any
--     -2 if unknown
rewrite_flags_in_lintype :: LinType -> QpState LinType
rewrite_flags_in_lintype (TArrow t u) = do
  t' <- rewrite_flags t
  u' <- rewrite_flags u
  return (TArrow t' u')

rewrite_flags_in_lintype (TTensor tlist) = do
  tlist' <- List.foldr (\t rec -> do
                          r <- rec
                          t' <- rewrite_flags t
                          return (t':r)) (return []) tlist
  return (TTensor tlist')  

rewrite_flags_in_lintype (TCirc t u) = do
  t' <- rewrite_flags t
  u' <- rewrite_flags u
  return (TCirc t' u')

rewrite_flags_in_lintype (TUser n args) = do
  args' <- List.foldr (\a rec -> do
                         r <- rec
                         a' <- rewrite_flags a
                         return (a':r)) (return []) args
  return (TUser n args')

rewrite_flags_in_lintype (TLocated t ex) = do
  set_location ex
  rewrite_flags_in_lintype t

rewrite_flags_in_lintype t =
  return t


-- | Replaces all the flag references by their actual value :
--     0 if no flag
--     1 of one
--     -1 of any
--     -2 if unknown
rewrite_flags :: Type -> QpState Type
rewrite_flags (TBang n t) = do
  t' <- rewrite_flags_in_lintype t
  if n < 2 then
    return (TBang n t')
  else do
    v <- flag_value n 
    case v of
      One ->
          return (TBang 1 t')
      Zero ->
          return (TBang 0 t')
      Any ->
          return (TBang (-1) t')
      Unknown ->
          return (TBang (-2) t')
        


-- | Generates a fresh type variable (linear type)
fresh_type :: QpState Variable
fresh_type = do
  ctx <- get_context
  id <- return $ type_id ctx
  set_context $ ctx { type_id = id + 1 }
  return id

-- | Generates a type of the form !n a, where n and a are fresh flag reference and type variable
new_type :: QpState Type
new_type = do
  x <- fresh_type
  f <- fresh_flag
  return (TBang f (TVar x))



-- | Throw a typing error, based on the reference flags of the faulty types
-- The return type can be anything, since an exception will be thrown in any case
throw_TypingError :: Type -> Type -> QpState a
throw_TypingError t@(TBang n _) u@(TBang m _) = do
  -- Retrieve the location / expression of the types
  termn <- referenced_expression n
  termm <- referenced_expression m

  -- Print the types t and u
  prt <- pprint_type_noref t
  pru <- pprint_type_noref u

  -- See what information we have
  case (termn, termm) of
    (Just (e, ex), _) -> do
        -- Print the expression / pattern
        pre <- case e of
                 ActualOfE e -> pprint_expr_noref e
                 ActualOfP p -> pprint_pattern_noref p

        f <- get_file
        throwQ $ DetailedTypingError prt pru pre (f, ex)

    (_, Just (e, ex)) -> do
        -- Print the expression / pattern
        pre <- case e of
                 ActualOfE e -> pprint_expr_noref e
                 ActualOfP p -> pprint_pattern_noref p

        f <- get_file
        throwQ $ DetailedTypingError pru prt pre (f, ex)
 
    _ ->
      -- No information available
      throwQ $ TypingError prt pru


-- | Throw a duplicable error, based on the faulty reference flags
throw_NonDuplicableError :: RefFlag -> QpState a
throw_NonDuplicableError ref = do
  -- Referenced expression / location
  term <- referenced_expression ref

  -- See what information we have
  case term of
    Just (e, ex) -> do
        pre <- case e of
                 ActualOfE e -> pprint_expr_noref e
                 ActualOfP p -> pprint_pattern_noref p
        f <- get_file
        throwQ $ NonDuplicableError pre (f, ex)

    Nothing -> do
        f <- get_file
        throwQ $ NonDuplicableError "(Unknown)" (f, extent_unknown)



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

map_lintype_step TInt = do
  return TInt

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

map_lintype_step (TUser typename arg) = do
  arg' <- List.foldr (\a rec -> do
                        r <- rec
                        a' <- map_type_step a
                        return (a':r)) (return []) arg
  return (TUser typename arg')


map_type_step (TBang f t) = do
  t' <- map_lintype_step t
  return $ TBang f t'

map_type_step (TForall fv ff cset typ) = do
  typ' <- map_type_step typ
  return $ TForall fv ff cset typ'

map_type t = do
  t' <- map_type_step t
  if t == t' then
    return t
  else
    map_type t'


-- | Complementary printing function for patterns and terms, that
-- replaces the references by their original name
pprint_pattern_noref :: Pattern -> QpState String
pprint_pattern_noref p = do
  nspace <- get_context >>= return . namespace
  fvar <- return (\x -> case IMap.lookup x $ N.varcons nspace of
                          Just n -> n
                          Nothing -> subvar 'x' x)
  fdata <- return (\d -> case IMap.lookup d $ N.datacons nspace of
                           Just n -> n
                           Nothing -> subvar 'D' d)
  return $ genprint Inf p [fvar, fdata]

-- | Same as pprint_pattern_noref
pprint_expr_noref :: Expr -> QpState String
pprint_expr_noref e = do
  nspace <- get_context >>= return . namespace
  fvar <- return (\x -> case IMap.lookup x $ N.varcons nspace of
                          Just n -> n
                          Nothing -> subvar 'x' x)
  fdata <- return (\d -> case IMap.lookup d $ N.datacons nspace of
                           Just n -> n
                           Nothing -> subvar 'D' d)
  return $ genprint Inf e [fvar, fdata]


-- | Same for types, the type variables are attributed names and printed
available_names :: [String]
available_names = ["a", "b", "c", "d", "a0", "a1", "a2", "b0", "b1", "b2"]

pprint_type_noref :: Type -> QpState String
pprint_type_noref t = do
  -- Printing of type variables
  fvt <- return $ free_typ_var t
  attr <- return $ List.zip fvt available_names
  fvar <- return (\x -> case List.lookup x attr of
                          Just n -> n
                          Nothing -> subvar 'X' x)

  -- Printing of flags
  refs <- get_context >>= return . flags
  fflag <- return (\f -> case f of
                           1 -> "!"
                           n | n >= 2 -> case IMap.lookup n refs of
                                           Just fi -> case value fi of
                                                        One -> "!"
                                                        _ -> ""
                                           Nothing -> ""
                             | otherwise -> "")
  return $ genprint Inf t [fflag, fvar]


