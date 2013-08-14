-- | This module contains the definition of the state monad used throughout the parsing, interpretation, typing, and more
-- generally all the processes working with the core syntax.
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
-- to a channel, which can be, for example, stdout, stderr, any file writing channel.
data Logfile = Logfile {
  channel :: Handle,
  verbose :: Int
}


-- | Enter a log with a given priority level.
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
  logfile :: Logfile,                                 -- ^ Log file currently in use.

-- Variable naming
  namespace :: Namespace,                             -- ^ Remembers the original names of the term variables (replaced by unique ids during the translation to the core syntax)

-- Location
  filename :: String,                                 -- ^ Path to the implementation of the module being processed.
  location :: Extent,                                 -- ^ Extent of the expression / type / pattern being studied.

-- Module related fields
  modules :: [(String, Module)],                      -- ^ The list of processed modules.
  cmodule :: Module,                                  -- ^ Definition of the current module.

-- Helpers of the typing / interpretation 
  builtins :: Map String (Type, Value),               -- ^ A certain number of functions / values are predefined and typed, those are put
                                                      -- in the builtins field, available to both typing and interpretation.
  types :: Map String Typespec,                       -- ^ Contains all the definition of both the imported types and the types defined in the current module.
  datacons :: IntMap Type,                            -- ^ The dataconstructors are considered as values, and so can be typed individually. This map contains
                                                      -- their type, as written in the type definition.
  globals :: IntMap Type,                             -- ^ Typing context correponding to the global variables imported from other modules.

-- Information relevant to flags
  flags :: IntMap FlagInfo,                           -- ^ Flags from types are references to this map, which holds information about the value of the flag, but
                                                      -- also about the type itself, for example the expression it is type of. Such information is useful to send
                                                      -- unambigous error messages when the type inference fails.

-- Circuit stack
  circuits :: [Circuit],                              -- ^ Stack of circuit used by the interpreter.

-- Id generation
  type_id :: Int,                                     -- ^ Used to generate fresh type variables.
  flag_id :: Int,                                     -- ^ Used to generate fresh flag references.
  qbit_id :: Int,                                     -- ^ Used to generate fresh quantum addresses. This field can be reinitialized (set to 0) after every new call to box[T].
     
-- Substitution from type variable to types
  mappings :: IntMap LinType                          -- ^ The result of the unification : a mapping from type variables to linear types.
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


-- | Throws an exception of type QError (exceptions specific to quipper).
throwQ :: QError -> QpState a
throwQ e =
  QpState { runS = (\ctx -> E.throw e) }


-- | Catches any error thrown in a certain computation, running a continuation in case
-- an error has been caught.
catchQ :: QpState a -> (QError -> QpState a) -> QpState a
catchQ st c =
  QpState { runS = (\ctx ->
                      (runS st ctx) `E.catch` (\e -> do
                                                 runS (c e) ctx)) }


-- | Relays actions from the IO monad to the QpState monad.
liftIO :: IO a -> QpState a
liftIO x = QpState { runS = (\ctx -> do
                               x' <- x
                               return (ctx, x')) }



-- | The initial context. Except from the logfile, set to print on the standard output (stdout), with the lowest verbose level (block everything),
-- everything is set to empty / 0 / [].
empty_context :: Context
empty_context =  Ctx {
-- The logfile is initialized to print on the standard output, with the lowest verbose level possible
  logfile = Logfile { channel = stdout, verbose = 0 },

-- The namespace is initially empty
  namespace = N.new_namespace,

-- No modules
  modules = [],
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

  circuits = [ Circ { qIn = [], gates = [], qOut = [] } ],

  flag_id = 2,   -- Flag ids 0 and 1 are reserved
  type_id = 0,
  qbit_id = 0,
      
  mappings = IMap.empty
}



-- | Returns the state context.
get_context :: QpState Context
get_context = QpState { runS = (\ctx -> return (ctx, ctx)) }


-- | Sets the state context.
set_context :: Context -> QpState ()
set_context ctx = QpState { runS = (\_ -> return (ctx, ())) }



-- | Changes the level of verbosity.
set_verbose :: Int -> QpState ()
set_verbose v = do
  ctx <- get_context
  set_context $ ctx { logfile = (logfile ctx) { verbose = v } }


-- | Enters a new log entry.
newlog :: Int -> String -> QpState ()
newlog lvl entry = do
  ctx <- get_context
  liftIO $ write_log (logfile ctx) lvl entry


-- | Flushes the log file.
flush_logs :: QpState ()
flush_logs = do
  ctx <- get_context
  liftIO $ hFlush (channel $ logfile ctx)




-- | Sets the location marker.
set_location :: Extent -> QpState ()
set_location ex = do
  ctx <- get_context
  set_context $ ctx { location = ex }


-- | Returns the current location marker.
get_location :: QpState Extent
get_location =
  get_context >>= return . location


-- | Changes the input file.
set_file :: String -> QpState ()
set_file fname = do
  ctx <- get_context
  set_context $ ctx { filename = fname }


-- | Returns the current input file.
get_file :: QpState String
get_file =
  get_context >>= return . filename




-- | Registers a variable in the namespace. A new id is generated, bound to
-- the given variable, and returned.
register_var :: String -> QpState Int
register_var x = do
  ctx <- get_context
  (id, nspace) <- return $ N.register_var x (namespace ctx)
  set_context $ ctx { namespace = nspace }
  return id


-- | Same as register_var, registers a data constructor. Note that the variable and datacon
-- ids may overlap, as they are generated from a different source.
register_datacon :: String -> Type -> QpState Int
register_datacon dcon dtype = do
  ctx <- get_context
  (id, nspace) <- return $ N.register_datacon dcon (namespace ctx)
  set_context $ ctx { namespace = nspace, datacons = IMap.insert id dtype $ datacons ctx }
  return id


-- | Creates a dummy variable from a new id n, registered under the name x_n.
dummy_var :: QpState Int
dummy_var = do
  ctx <- get_context
  (id, nspace) <- return $ N.dummy_var (namespace ctx)
  set_context $ ctx { namespace = nspace }
  return id


-- | Retrieves the name of the given variable. If no match is found in
-- the namespace, a standard name x_n is produced.
variable_name :: Variable -> QpState String
variable_name x = do
  ctx <- get_context
  case IMap.lookup x $ N.varcons (namespace ctx) of
    Just n ->
        return n

    Nothing ->
        return $ subvar 'x' x


-- | Retrives the name of the given data constructor. Again, if no match is found in
-- the namespace, a standard name D_n is produced.
datacon_name :: Variable -> QpState String
datacon_name x = do
  ctx <- get_context
  case IMap.lookup x $ N.datacons (namespace ctx) of
    Just n ->
        return n

    Nothing ->
        return $ subvar 'D' x




-- | Returns the current module.
get_module :: QpState Module
get_module =
  get_context >>= return . cmodule


-- | Sets the current module.
set_module :: Module -> QpState ()
set_module m = do
  ctx <- get_context
  set_context $ ctx { cmodule = m }


-- | Request for a variable to be exported (added to the current module export list).
-- New entries are added in the definition of the current module in the ids, types and vars maps.
-- Note that the type is initialized with the default value 'T', and the value with the default '()'.
export_var :: Variable -> QpState ()
export_var x = do
  -- Current module
  cm <- get_module
  -- Name of the variable
  name <- variable_name x

  set_module $ cm { global_ids = Map.insert name x $ global_ids cm,
                    global_types = IMap.insert x (TBang (-1) TUnit) $ global_types cm,
                    global_vars = IMap.insert x VUnit $ global_vars cm }


-- | Updates the type of a global variable from the current module.
update_global_type :: Variable -> Type -> QpState ()
update_global_type x t = do
  m <- get_module
  set_module $ m { global_types = IMap.update (\_ -> Just t) x $ global_types m }


-- | Creates the initializer of the interpretation : creates an evaluation context in which
-- all the global variables from the module dependencies have been inserted, associated with their
-- respective value.
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


-- | Create the initializer of the translation into internal syntax : returns the namespace in which
-- all the global variables from the module dependencies have inserted, associated with their respective
-- inferred type.
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




-- | Registers the definition of a type.
register_type :: String -> Typespec -> QpState ()
register_type typ spec = do
  ctx <- get_context
  set_context $ ctx { types = Map.insert typ spec $ types ctx }


-- | Imports the global variables and types from the module dependencies in the globals field.
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


-- | Looks up the type of a global variable.
type_of_global :: Variable -> QpState Type
type_of_global x = do
  ctx <- get_context
  case IMap.lookup x $ globals ctx of
    Just t ->
        return t
    Nothing -> do
        n <- variable_name x
        throwQ $ ProgramError $ "undefined global variable " ++ n


-- | Looks up a variable in a specific module (typically used with a qualified variable).
-- The input pair is (Module, Var name).
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
                f <- return $ filepath (cmodule ctx)
                throwQ $ LocatedError (UnboundVariable (mod ++ "." ++ n)) (f, ex)

      Nothing -> do
          ex <- get_location
          f <- return $ filepath (cmodule ctx)
          throwQ $ LocatedError (UnboundVariable (mod ++ "." ++ n)) (f, ex)

  else do
    ex <- get_location
    f <- return $ filepath (cmodule ctx)
    throwQ $ LocatedError (UnboundVariable (mod ++ "." ++ n)) (f, ex)


-- | Looks up a type from a specific module (typically used with a qualified type name).
-- The input name is (Module, Type name).
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
                f <- return $ filepath (cmodule ctx)
                throwQ $ LocatedError (UnboundVariable (mod ++ "." ++ n)) (f, ex)

      Nothing -> do
          ex <- get_location
          f <- return $ filepath (cmodule ctx)
          throwQ $ LocatedError (UnboundVariable (mod ++ "." ++ n)) (f, ex)

  else do
    ex <- get_location
    f <- return $ filepath (cmodule ctx)
    throwQ $ LocatedError (UnboundVariable (mod ++ "." ++ n)) (f, ex)


-- | Looks up the type of a builtin object.
builtin_type :: String -> QpState Type
builtin_type s = do
  ctx <- get_context
  case Map.lookup s $ builtins ctx of
    Just (t, _) ->
        return t
    Nothing ->
        throwQ $ ProgramError $ "Missing builtin: " ++ s


-- | Looks up the value of a builtin object.
builtin_value :: String -> QpState Value
builtin_value s = do
  ctx <- get_context
  case Map.lookup s $ builtins ctx of
    Just (_, v) ->
        return v
    Nothing ->
        throwQ $ ProgramError $ "Missing builtin: " ++ s


-- | Checks whether the input string corresponds to a (algebraic) type name.
exist_type :: String -> QpState Bool
exist_type typename = do
  ctx <- get_context
  return $ Map.member typename $ types ctx


-- | Retrieves the definition of a type.
type_spec :: String -> QpState Typespec
type_spec typ = do
  ctx <- get_context
  case Map.lookup typ $ types ctx of
    Just n ->
        return n

    Nothing ->
        throwQ $ ProgramError $ "Missing the definition of the type: " ++ typ


-- | Retrieves the definition of a datacon.
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





-- | Access to the information held by flags.
-- Returns the current value of a flag given by its reference.
flag_value :: RefFlag -> QpState FlagValue
flag_value ref =
  case ref of
    0 -> return Zero
    1 -> return One
    _ -> do
        ctx <- get_context
        case IMap.lookup ref $ flags ctx of
          Just info ->
              return $ value info

          Nothing ->
              throwQ $ ProgramError $ "Undefined flag reference: " ++ subvar 'f' ref



-- | Set the value of the flag to one.
-- If the value previously recorded is incompatible with the new one, an error is generated (eg : old val = Zero).
set_flag :: RefFlag-> QpState ()
set_flag ref = do
  case ref of
    0 -> do
        f <- get_file
        throwQ $ LocatedError (NonDuplicableError "(unknown)") (f, extent_unknown)
    1 -> return ()
    _ -> do
        ctx <- get_context 
        case IMap.lookup ref $ flags ctx of
          Just info -> do
              case value info of
                Zero -> do
                    throw_NonDuplicableError ref
                Unknown ->
                    set_context $ ctx { flags = IMap.insert ref (info { value = One }) $ flags ctx }
                _ ->
                    return ()  -- Includes anyflag and one

          Nothing ->
              throwQ $ ProgramError $ "Undefined flag reference: " ++ subvar 'f' ref


-- | Set the value of the flag to zero.
-- If the value previously recorded is incompatible with the new one, an error is generated (eg : old val = One).
unset_flag :: RefFlag -> QpState ()
unset_flag ref = do
  case ref of
    (-1) -> return ()
    0 -> return ()
    1 -> do
        f <- get_file
        throwQ $ LocatedError (NonDuplicableError "(unknown)") (f, extent_unknown)
    _ -> do
        ctx <- get_context 
        case IMap.lookup ref $ flags ctx of
          Just info -> do
              case value info of
                One ->
                    throw_NonDuplicableError ref
                Unknown ->
                    set_context $ ctx { flags = IMap.insert ref (info { value = Zero }) $ flags ctx }
                _ ->
                    return ()  -- Includes anyflag and zero

          Nothing ->
              throwQ $ ProgramError $ "Undefined flag reference: " ++ subvar 'f' ref


-- | Generates a new flag reference, and add its accompying binding in the flags map.
-- The flag is initially set to Unknown, with no expression or location.
fresh_flag :: QpState RefFlag
fresh_flag = do
  ctx <- get_context
  id <- return $ flag_id ctx
  set_context $ ctx { flag_id = id + 1,
                      flags = IMap.insert id (FInfo { value = Unknown }) $ flags ctx }
  return id 


-- | Generates a new flag reference, and add its accompying binding in the flags map.
-- The value of the new flag is set to the specified one, but it is still un-located.
fresh_flag_with_value :: FlagValue -> QpState RefFlag
fresh_flag_with_value v = do
  ctx <- get_context
  id <- return $ flag_id ctx
  set_context $ ctx { flag_id = id + 1,
                      flags = IMap.insert id (FInfo { value = v }) $ flags ctx }
  return id 


-- | Creates a new flag reference, initialized with the information
-- referenced by the argument flag.
duplicate_flag :: RefFlag -> QpState RefFlag
duplicate_flag ref = do
  case ref of
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





-- | Generic type instanciation.
-- New variables are produced for every one generalized over, and substituted to the old ones in the type and the constraints.
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


-- | If the type is generic, then it instanciates the typing scheme, else it just returns the type.
instanciate :: Type -> QpState (Type, ConstraintSet)
instanciate (TForall refs vars cset typ) =
  instanciate_scheme refs vars cset typ

instanciate typ =
  return (typ, emptyset)


-- | Replaces in linear types all the flag references by their actual value :
--     0 if no flag,
--     1 of one,
--     -1 of any,
--     -2 if unknown.
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

rewrite_flags_in_lintype t =
  return t


-- | Replaces in types all the flag references by their actual value :
--     0 if no flag,
--     1 of one,
--     -1 of any,
--     -2 if unknown.
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
      Unknown ->
          return (TBang (-2) t')
        



-- | Generates a fresh type variable.
fresh_type :: QpState Variable
fresh_type = do
  ctx <- get_context
  id <- return $ type_id ctx
  set_context $ ctx { type_id = id + 1 }
  return id


-- | Generates a type of the form !n a, where n and a are fresh flag reference and type variable.
new_type :: QpState Type
new_type = do
  x <- fresh_type
  f <- fresh_flag
  return (TBang f (TVar x))




-- | Throws a typing error, based on the reference flags of the faulty types.
-- The return type can be anything, since an exception will be thrown in any case.
throw_TypingError :: LinType -> LinType -> ConstraintInfo -> QpState a
throw_TypingError t u info = do
  -- Print the types t and u
  prt <- pprint_lintype_noref t
  pru <- pprint_lintype_noref u

  -- Get the location / expression
  f <- get_file
  ex <- return $ loc info
  expr <- pprint_expr_noref $ expression info
  
  -- Get the original type
  ori <- case in_type info of
           Just a -> do
               p <- pprint_lintype_noref a
               return $ Just p
           Nothing ->
               return $ Nothing

  -- Check which of the type is the actual one
  if actual info then
    throwQ $ LocatedError (DetailedTypingError prt pru ori expr) (f, ex)
  else
    throwQ $ LocatedError (DetailedTypingError pru prt ori expr) (f, ex)



-- | Throw a duplicable error, based on the faulty reference flag.
throw_NonDuplicableError :: RefFlag -> QpState a
throw_NonDuplicableError ref = do
  f <- get_file
  throwQ $ LocatedError (NonDuplicableError "(Unknown)") (f, extent_unknown)




-- | Inserts a new mapping x |-> t in the substitution, where x is a type variable and t a linear type.
mapsto :: Variable -> LinType -> QpState ()
mapsto x t = do
  ctx <- get_context
  set_context $ ctx { mappings = IMap.insert x t $ mappings ctx }


-- | Looks for a mapping of the argument variable. The function never fails, as of no mapping
-- is found for x, the linear type 'x' is returned.
appmap :: Variable -> QpState LinType
appmap x = do
  ctx <- get_context
  case IMap.lookup x $ mappings ctx of
    Just t -> return t
    Nothing -> return $ TVar x


-- | Recursively applies the mappings recorded in the current state to a linear type.
map_lintype :: LinType -> QpState LinType
map_lintype (TVar x) = do
  t <- appmap x
  case t of
    -- If the value of x has been changed, reapply the mapping function, else returns the original type.
    TVar y | y /= x -> map_lintype (TVar y)
           | otherwise -> return (TVar x)
    t -> map_lintype t

map_lintype (TArrow t u) = do
  t' <- map_type t
  u' <- map_type u
  return (TArrow t' u')

map_lintype (TTensor tlist) = do
  tlist' <- List.foldr (\t rec -> do
                          r <- rec
                          t' <- map_type t
                          return (t':r)) (return []) tlist
  return (TTensor tlist')

map_lintype (TCirc t u) = do
  t' <- map_type t
  u' <- map_type u
  return (TCirc t' u')

map_lintype (TUser typename arg) = do
  arg' <- List.foldr (\a rec -> do
                        r <- rec
                        a' <- map_type a
                        return (a':r)) (return []) arg
  return (TUser typename arg')

-- The remainging linear types are unit bool qbit and int, and mapped to themselves.
map_lintype typ = do
  return typ


-- | Recursively applies the mappings recorded in the current state to a linear type.
map_type :: Type -> QpState Type
map_type (TBang f t) = do
  t' <- map_lintype t
  v <- flag_value f
  case v of
    One -> return $ TBang 1 t'
    Zero -> return $ TBang 0 t'
    _ -> return $ TBang f t'

map_type (TForall fv ff cset typ) = do
  typ' <- map_type typ
  return $ TForall fv ff cset typ'


-- | Checks wheter a linear type is a quantum data type or not.
is_qdata_lintype :: LinType -> QpState Bool
is_qdata_lintype TQbit =
  return True

is_qdata_lintype TUnit =
  return True

is_qdata_lintype (TTensor tlist) =
  List.foldl (\rec t -> do
                b <- rec
                if b then
                  is_qdata_type t
                else
                  return False) (return True) tlist

is_qdata_lintype (TUser typename args) = do
  spec <- type_spec typename
  case qdatatype spec of
    True ->
        List.foldl (\rec t -> do
                      b <- rec
                      if b then
                        is_qdata_type t
                      else
                        return False) (return True) args
    False ->
        return False

is_qdata_lintype _ =
  return False


-- | Checks whether a type is a quantum data type or not.
is_qdata_type :: Type -> QpState Bool
is_qdata_type (TBang _ a) =
  is_qdata_lintype a



-- | Complementary printing function for patterns and terms, that
-- replaces the references by their original name.
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


-- | Same as pprint_pattern_noref.
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


-- | List of names, to be used to represent type variables.
available_names :: [String]
available_names = ["a", "b", "c", "d", "a0", "a1", "a2", "b0", "b1", "b2"]


-- | The type variables are attributed random names before being printed, and the flags are
-- printed with their actual value : only if the flag is set will it be displayed as '!', else it will appear as ''.
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


-- | Same as pprint_type_noref.
pprint_lintype_noref :: LinType -> QpState String
pprint_lintype_noref a = do
  -- Printing of type variables
  fva <- return $ free_typ_var a
  attr <- return $ List.zip fva available_names
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
  return $ genprint Inf a [fflag, fvar]



-- | Same as pprint_expr_noref.
pprint_value_noref :: Value -> QpState String
pprint_value_noref v = do
  nspace <- get_context >>= return . namespace
  -- Printing of data constructors
  fdata <- return (\d -> case IMap.lookup d $ N.datacons nspace of
                           Just n -> n
                           Nothing -> subvar 'D' d)

  return $ genprint Inf v [fdata]
