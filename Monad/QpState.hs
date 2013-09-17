-- | This module defines the state monad that is used throughout the parsing, interpretation, typing, and more
-- generally all the processes working with the core syntax.
module Monad.QpState where

import Utils
import Classes
import Builtins

import Parsing.Location (Extent, extent_unknown, file_unknown)

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



-- | A data type to implement a logger. Logs can be given different priorities, depending on their importance.
-- The verbose control then discards any log whose priority is lower than the control. The logs are printed
-- to a channel, which can be, for example, 'stdout', 'stderr', or any file writing channel.
data Logfile = Logfile {
  channel :: Handle,
  verbose :: Int
}


-- | Log a message with a given priority level.
write_log :: Logfile -> Int -> String -> IO ()
write_log logfile lvl s = do
  w <- hIsWritable $ channel logfile
  if lvl >= verbose logfile || not w then
    return ()
  else do
    hPutStrLn (channel logfile) s
    hFlush (channel logfile)



-- | The context of a Quipper function. This is the context in which all Quipper functions are evaluated. It is used
-- from parsing to interpretation and type inference. We prefer using a single context to using
-- several module-specific contexts, to avoid having to convey information between different kinds of state. 
-- This also means that all the data structures required by each module must be included in the context, which now
-- contains:
-- 
-- *  A logfile, used for regular and debug printing.
-- 
-- *  Information relevant to the original expression (location in file, sample of the current expression).
-- 
-- *  A namespace to record the variables of the original expression.
-- 
-- *  The definition of the user types, recorded as a map mapping each data constructor to the argument type and the data type it is part of.
-- 
-- *  For the interpreter: an evaluation context, including the current circuit and mappings.

data Context = Ctx {

-- Log file  
  logfile :: Logfile,                                 -- ^ Log file currently in use.

-- Variable naming
  namespace :: Namespace,                             -- ^ Remembers the original names of the term variables (replaced by unique ids during the translation to the core syntax).

-- Location
  filename :: String,                                 -- ^ Path to the implementation of the module being processed.
  location :: Extent,                                 -- ^ Extent of the expression \/ type \/ pattern being studied.

-- Module related fields
  modules :: [(String, Module)],                      -- ^ The list of processed modules. The module definition defines an interface to the module.
  dependencies :: [String],                           -- ^ The list of modules currently accessible (a subset of modules).

-- Helpers of the typing / interpretation 
  types :: IntMap (Either Typedef Typesyn),           -- ^ The definitions of both the imported types and the types defined in the current module.

  builtins :: Map String (Type, Value),               -- ^ A certain number of predefined and pre-typed functions \/ values are put
                                                      -- in the 'builtins' field, where they are available to both the type checker and the interpreter.
  datacons :: IntMap TypeScheme,                      -- ^ Data constructors are considered to be values, and so can be typed individually. This map contains
                                                      -- their type, as written in the type definition.
  globals :: IntMap TypeScheme,                       -- ^ Typing context corresponding to the global variables imported from other modules.

  values :: IntMap Value,                             -- ^ The values of the global variables.

-- Information relevant to flags
  flags :: IntMap FlagInfo,                           -- ^ Flags from types are references to this map, which holds information about the value of the flag, but
                                                      -- also about the type itself, for example the expression it is the type of. Such information is useful to send
                                                      -- unambiguous error messages when the type inference fails.

-- Circuit stack
  circuits :: [Circuit],                              -- ^ The circuit stack used by the interpreter.

-- Id generation
  type_id :: Int,                                     -- ^ Used to generate fresh type variables.
  flag_id :: Int,                                     -- ^ Used to generate fresh flag references.
  qubit_id :: Int,                                    -- ^ Used to generate fresh quantum addresses. This field can be reinitialized (set to 0) after every new call to box[T].
     
-- Substitution from type variable to types
  mappings :: IntMap LinType                          -- ^ The result of the unification: a mapping from type variables to linear types.
}



-- | The state monad associated with a 'Context'.
-- The monad runs its operations in the 'IO' monad, so it can perform input \/ output operations
-- via a simple lift.
newtype QpState a = QpState { runS :: (Context -> IO (Context, a)) }

instance Monad QpState where
  return a = QpState { runS = (\ctx -> return (ctx, a)) }
  fail s = QpState { runS = (\ctx -> fail s) }
  st >>= action = QpState { runS = (\ctx -> do
                                    (ctx', a) <- runS st ctx 
                                    st' <- return $ action a
                                    runS st' ctx') }


-- | Throw an exception of type 'QError' (exceptions specific to Quipper).
throwQ :: QError -> QpState a
throwQ e =
  QpState { runS = (\ctx -> E.throw e) }


-- | Catch any error thrown in a certain computation, and run a continuation in case
-- an error is caught.
catchQ :: QpState a -> (QError -> QpState a) -> QpState a
catchQ st c =
  QpState { runS = (\ctx ->
                      (runS st ctx) `E.catch` (\e -> do
                                                 runS (c e) ctx)) }


-- | Relay actions from the 'IO' monad to the 'QpState' monad.
liftIO :: IO a -> QpState a
liftIO x = QpState { runS = (\ctx -> do
                               x' <- x
                               return (ctx, x')) }



-- | The initial context. Except for the logfile, which is set to print on standard output (stdout) with the lowest verbose level (block everything),
-- everything else is set to empty \/ 0 \/ [].
empty_context :: Context
empty_context =  Ctx {
-- The logfile is initialized to print on the standard output, with the lowest verbose level possible
  logfile = Logfile { channel = stdout, verbose = 0 },

-- The namespace is initially empty
  namespace = N.new_namespace,

-- No modules
  modules = [],
  dependencies = [],
 
-- No global variables
  globals = IMap.empty,
  values = IMap.empty, 

-- No builtins, added later
  builtins = Map.empty,

-- The initial location is unknown, as well as the name of the code file
  filename = file_unknown,
  location = extent_unknown,

-- No predefined types, datacons or flags
  types = IMap.empty,
  datacons = IMap.empty,

-- No flag
  flags = IMap.empty,

-- Circuit stack initialized with a void circuit.
  circuits = [ Circ { qIn = [], gates = [], qOut = [], Interpret.Circuits.qubit_id = 0, unused_ids = [] } ],

  flag_id = 2,   -- Flag ids 0 and 1 are reserved
  type_id = 0,
  Monad.QpState.qubit_id = 0,
      
  mappings = IMap.empty
}



-- | Return the state context.
get_context :: QpState Context
get_context = QpState { runS = (\ctx -> return (ctx, ctx)) }


-- | Set the state context.
set_context :: Context -> QpState ()
set_context ctx = QpState { runS = (\_ -> return (ctx, ())) }



-- | Change the level of verbosity.
set_verbose :: Int -> QpState ()
set_verbose v = do
  ctx <- get_context
  set_context $ ctx { logfile = (logfile ctx) { verbose = v } }


-- | Enter a new log entry.
newlog :: Int -> String -> QpState ()
newlog lvl entry = do
  ctx <- get_context
  liftIO $ write_log (logfile ctx) lvl entry


-- | Flush the log file.
flush_logs :: QpState ()
flush_logs = do
  ctx <- get_context
  liftIO $ hFlush (channel $ logfile ctx)




-- | Set the location marker.
set_location :: Extent -> QpState ()
set_location ex = do
  ctx <- get_context
  set_context $ ctx { location = ex }


-- | Return the current location marker.
get_location :: QpState Extent
get_location =
  get_context >>= return . location


-- | Change the input file.
set_file :: String -> QpState ()
set_file fname = do
  ctx <- get_context
  set_context $ ctx { filename = fname }


-- | Return the current input file.
get_file :: QpState String
get_file =
  get_context >>= return . filename




-- | Register a variable in the namespace. A new id is generated, bound to
-- the given variable, and returned.
register_var :: String -> Extent -> QpState Int
register_var x ex = do
  ctx <- get_context
  (id, nspace) <- return $ N.register_var x ex (namespace ctx)
  set_context $ ctx { namespace = nspace }
  return id


-- | Like 'register_var', but register a data constructor. Note that the variable and data constructor
-- ids may overlap, as they are generated from a different source.
register_datacon :: String -> TypeScheme -> QpState Int
register_datacon dcon dtype = do
  ctx <- get_context
  (id, nspace) <- return $ N.register_datacon dcon (namespace ctx)
  set_context $ ctx { namespace = nspace,
                      datacons = IMap.insert id dtype $ datacons ctx }
  return id


-- | Register a data type definition. A unique id is attributed to the type name and returned.
register_typedef :: String -> Typedef -> QpState Int
register_typedef typename def = do
  ctx <- get_context
  (id, nspace) <- return $ N.register_type typename (namespace ctx)
  set_context $ ctx { namespace = nspace,
                      types = IMap.insert id (Left def) $ types ctx }
  return id


-- | Register a type synonym.
register_typesyn :: String -> Typesyn -> QpState Int
register_typesyn typename syn = do
  ctx <- get_context
  (id, nspace) <- return $ N.register_type typename (namespace ctx)
  set_context $ ctx { namespace = nspace,
                      types = IMap.insert id (Right syn) $ types ctx }
  return id


-- | Create a dummy variable from a new id /n/, registered under the name /x_n/.
dummy_var :: QpState Int
dummy_var = do
  ctx <- get_context
  (id, nspace) <- return $ N.dummy_var (namespace ctx)
  set_context $ ctx { namespace = nspace }
  return id


-- | Retrieve the name of the given variable. If no match is found in
-- the namespace, produce a standard name /x_n/.
variable_name :: Variable -> QpState String
variable_name x = do
  ctx <- get_context
  case IMap.lookup x $ N.varcons (namespace ctx) of
    Just n ->
        return n

    Nothing ->
        return $ subvar 'x' x


-- | Retrieve the location of the variable declaration. If no match is found, return the default
-- extent 'extent_unknown'.
variable_location :: Variable -> QpState Extent
variable_location x = do
  ctx <- get_context
  case IMap.lookup x $ N.varloc (namespace ctx) of
    Just ex -> return ex
    Nothing -> return extent_unknown


-- | Retrieve the name of the given data constructor. If no match is found in
-- the namespace, produce a standard name /D_n/.
datacon_name :: Variable -> QpState String
datacon_name x = do
  ctx <- get_context
  case IMap.lookup x $ N.datacons (namespace ctx) of
    Just n ->
        return n

    Nothing ->
        return $ subvar 'D' x


-- | Retrieve the name of the given type. If no match is found in
-- the namespace, produce a standard name /A_n/.
type_name :: Variable -> QpState String
type_name x = do
  ctx <- get_context
  case IMap.lookup x $ N.typecons (namespace ctx) of
    Just n ->
        return n

    Nothing ->
        return $ subvar 'A' x


-- | Create the initializer of the translation into internal syntax. This returns the namespace in which
-- all the global variables and data constructors from the module dependencies have been inserted, associated with their respective
-- inferred type.
global_namespace :: [String]                                                          -- ^ A list of module dependencies.
                 -> QpState (Map String LVariable, Map String Int, Map String Type)   -- ^ The resulting labelling maps.
global_namespace deps = do
  mods <- get_context >>= return . modules
  List.foldl (\rec m -> do
                (lblv, lbld, lblt) <- rec
                case List.lookup m mods of
                  Just mod -> do
                      vars <- return $ Map.map (\id -> LGlobal id) $ m_variables mod
                      typs <- return $ Map.map (\id -> TBang 0 $ TUser id []) $ m_types mod
                      return (Map.union vars lblv, Map.union (m_datacons mod) lbld, Map.union typs lblt)

                  Nothing ->
                      throwQ $ ProgramError $ "missing implementation of module " ++ m) (return (Map.empty, Map.empty, Map.empty)) deps




-- | Look up the type of a global variable.
type_of_global :: Variable -> QpState TypeScheme
type_of_global x = do
  ctx <- get_context
  case IMap.lookup x $ globals ctx of
    Just t ->
        return t
    Nothing -> do
        n <- variable_name x
        throwQ $ ProgramError $ "undefined global variable " ++ n




-- | Look up a variable in a specific module (typically used with a qualified variable).
-- The input pair is (Module, Var name).
lookup_qualified_var :: (String, String) -> QpState Variable
lookup_qualified_var (mod, n) = do
  ctx <- get_context
  -- Check that the module is part of the M.dependencies
  if List.elem mod $ dependencies ctx then do
    case List.lookup mod $ modules ctx of
      Just modi -> do
          case Map.lookup n $ m_variables modi of
            Just x -> return x
            Nothing -> do
                throw_UnboundVariable (mod ++ "." ++ n)

      Nothing -> do
          throw_UnboundVariable (mod ++ "." ++ n)

  else do
    throw_UnboundVariable (mod ++ "." ++ n)



-- | Look up a type from a specific module (typically used with a qualified type name).
-- The input name is (Module, Type name).
lookup_qualified_type :: (String, String) -> QpState Variable
lookup_qualified_type (mod, n) = do
  ctx <- get_context
  -- Check that the module is part of the M.dependencies
  if List.elem mod $ dependencies ctx then do
    case List.lookup mod $ modules ctx of
      Just modi -> do
          case Map.lookup n $ m_types modi of
            Just x -> return x
            Nothing -> do
                throw_UndefinedType (mod ++ "." ++ n)

      Nothing -> do
          throw_UndefinedType (mod ++ "." ++ n)

  else do
    throw_UndefinedType (mod ++ "." ++ n)



-- | Look up the type of a built-in object.
builtin_type :: String -> QpState Type
builtin_type s = do
  ctx <- get_context
  case Map.lookup s $ builtins ctx of
    Just (t, _) -> do
        (ff, fv) <- return (free_flag t, free_typ_var t)
        -- Replace the flags
        t <- List.foldl (\rec f -> do
                           typ <- rec
                           f' <- fresh_flag
                           return $ subs_flag f f' typ) (return t) ff
        -- Replace the type variables
        t <- List.foldl (\rec v -> do
                           typ <- rec
                           v' <- fresh_type
                           return $ subs_typ_var v (TVar v') typ) (return t) fv
        return t
    Nothing ->
        throwQ $ ProgramError $ "Missing builtin: " ++ s



-- | Look up the value of a built-in object.
builtin_value :: String -> QpState Value
builtin_value s = do
  ctx <- get_context
  case Map.lookup s $ builtins ctx of
    Just (_, v) ->
        return v
    Nothing ->
        throwQ $ ProgramError $ "Missing builtin: " ++ s



-- | Retrieve the definition of a type.
type_spec :: Variable -> QpState (Either Typedef Typesyn)
type_spec typ = do
  ctx <- get_context
  case IMap.lookup typ $ types ctx of
    Just n ->
        return n

    Nothing -> do
        n <- type_name typ
        throwQ $ ProgramError $ "Missing the definition of the type: " ++ n


-- | Retrieve the definition of a data constructor.
datacon_def :: Int -> QpState TypeScheme
datacon_def id = do
  ctx <- get_context
  case IMap.lookup id $ datacons ctx of
    Just def ->
        return def
  
    Nothing ->
        -- The sound definition of the data constructors has already been checked
        -- during the translation into the core syntax
        throwQ $ ProgramError $ "Missing the definition of data constructor: " ++ subvar 'D' id





-- | Access the information held by a flag.
-- Returns the current value of the flag given by its reference.
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



-- | Set the value of a flag to one.
-- If the previously recorded value is incompatible with the new one, generate an error (i.e.., old val = Zero).
set_flag :: RefFlag -> ConstraintInfo -> QpState ()
set_flag ref info = do
  case ref of
    0 -> do
        throw_NonDuplicableError info
    1 -> return ()
    _ -> do
        ctx <- get_context 
        case IMap.lookup ref $ flags ctx of
          Just i -> do
              case value i of
                Zero -> do
                    case in_type info of
                      Just a -> do
                          a0 <- return $ subs_flag ref 0 a
                          a1 <- return $ subs_flag ref 1 a
                          throw_TypingError a0 a1 info { actual = True }
                      Nothing ->
                          throw_NonDuplicableError info
                Unknown ->
                    set_context $ ctx { flags = IMap.insert ref (i { value = One }) $ flags ctx }
                _ ->
                    return ()  -- Includes anyflag and one

          Nothing ->
              throwQ $ ProgramError $ "Undefined flag reference: " ++ subvar 'f' ref


-- | Set the value of a flag to zero.
-- If the previously recorded value is incompatible with the new one, generate an error (i.e., old val = One).
unset_flag :: RefFlag -> ConstraintInfo -> QpState ()
unset_flag ref info = do
  case ref of
    0 -> return ()
    1 -> do
        throw_NonDuplicableError info
    _ -> do
        ctx <- get_context 
        case IMap.lookup ref $ flags ctx of
          Just i -> do
              case value i of
                One ->
                    case in_type info of
                      Just a -> do
                          a0 <- return $ subs_flag ref 0 a
                          a1 <- return $ subs_flag ref 1 a
                          throw_TypingError a0 a1 info { actual = False, in_type = Nothing }
                      Nothing ->
                          throw_NonDuplicableError info
                Unknown ->
                    set_context $ ctx { flags = IMap.insert ref (i { value = Zero }) $ flags ctx }
                _ ->
                    return ()  -- Includes anyflag and zero

          Nothing ->
              throwQ $ ProgramError $ "Undefined flag reference: " ++ subvar 'f' ref


-- | Generate a new flag reference, and add its accompanying binding to the flags map.
-- The flag is initially set to 'Unknown', with no expression or location.
fresh_flag :: QpState RefFlag
fresh_flag = do
  ctx <- get_context
  id <- return $ flag_id ctx
  set_context $ ctx { flag_id = id + 1,
                      flags = IMap.insert id (FInfo { value = Unknown }) $ flags ctx }
  return id 


-- | Generate a new flag reference, and add its accompanying binding to the flags map.
-- The new flag is set to the specified value, but it is still un-located.
fresh_flag_with_value :: FlagValue -> QpState RefFlag
fresh_flag_with_value v = do
  ctx <- get_context
  id <- return $ flag_id ctx
  set_context $ ctx { flag_id = id + 1,
                      flags = IMap.insert id (FInfo { value = v }) $ flags ctx }
  return id 


-- | Create a new flag reference, initialized with the information
-- of the argument flag.
duplicate_flag :: RefFlag -> QpState RefFlag
duplicate_flag ref = do
  case ref of
    0 -> return 0
    1 -> return 1
    _ -> do
        ctx <- get_context
        id <- return $ flag_id ctx
        case IMap.lookup ref $ flags ctx of
          Just info -> do
              set_context $ ctx { flag_id = id + 1,
                                  flags = IMap.insert id info $ flags ctx }
              return id

          Nothing ->
              throwQ $ ProgramError $ "Undefined flag reference: " ++ subvar 'f' ref





-- | Generic type instantiation.
-- Produce a new variable for every one generalized over, and substitute it for the old ones in the type and the constraints.
instantiate_scheme :: [RefFlag] -> [Variable] -> ConstraintSet -> Type -> QpState (Type, ConstraintSet)
instantiate_scheme refs vars cset typ = do
  -- Replace the flag references by new ones
  (typ', cset') <- List.foldl (\rec ref -> do
                                 (typ, cset) <- rec
                                 nref <- duplicate_flag ref
                                 typ' <- return $ subs_flag ref nref typ
                                 cset' <- return $ subs_flag ref nref cset
                                 return (typ', cset')) (return (typ, cset)) refs

  -- Replace the variables
  (typ', cset') <- List.foldl (\rec var -> do
                                 (typ, cset) <- rec
                                 nvar <- fresh_type
                                 typ' <- return $ subs_typ_var var (TVar nvar) typ
                                 cset' <- return $ subs_typ_var var (TVar nvar) cset
                                 return (typ', cset')) (return (typ', cset')) vars

  return (typ', cset')

-- | Instantiate the typing scheme.
instantiate :: TypeScheme -> QpState (Type, ConstraintSet)
instantiate (TForall refs vars cset typ) =
  instantiate_scheme refs vars cset typ


-- | In a linear type, replace all the flag references by their actual value:
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


-- | In a type, replace all the flag references by their actual value:
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


-- | Generate a fresh type variable.
fresh_type :: QpState Variable
fresh_type = do
  ctx <- get_context
  id <- return $ type_id ctx
  set_context $ ctx { type_id = id + 1 }
  return id


-- | Generate a type of the form !/n a/, where /n/ and /a/ are a fresh flag reference and a type variable.
new_type :: QpState Type
new_type = do
  x <- fresh_type
  f <- fresh_flag
  return (TBang f (TVar x))




-- | Throw a typing error, based on the reference flags of the faulty types.
-- The return type can be anything, since an exception will be thrown in any case.
throw_TypingError :: Type -> Type -> ConstraintInfo -> QpState a
throw_TypingError t u info = do
  -- Print the types t and u
  prt <- pprint_type_noref t
  pru <- pprint_type_noref u

  -- Get the location / expression
  ex <- return $ loc info
  expr <- pprint_expr_noref $ expression info
  
  -- Get the original type
  ori <- case in_type info of
           Just a -> do
               p <- pprint_type_noref a
               return $ Just p
           Nothing ->
               return $ Nothing

  -- Check which of the type is the actual one
  if actual info then
    throwQ $ LocatedError (DetailedTypingError prt pru ori expr) ex
  else
    throwQ $ LocatedError (DetailedTypingError pru prt ori expr) ex



-- | Generic error for unbound values (variables, data constructors, types, builtins).
throw_UnboundValue :: String -> (String -> QError) -> QpState a
throw_UnboundValue v err = do
  ex <- get_location
  throwQ $ LocatedError (err v) ex


-- | Throw an unbound variable error.
throw_UnboundVariable :: String -> QpState a
throw_UnboundVariable n =
  throw_UnboundValue n UnboundVariable


-- | Throw an unbound data constructor error.
throw_UnboundDatacon :: String -> QpState a
throw_UnboundDatacon n =
  throw_UnboundValue n UnboundDatacon


-- | Throw an undefined type error.
throw_UndefinedType :: String -> QpState a
throw_UndefinedType n =
  throw_UnboundValue n UndefinedType


-- | Throw an undefined builtin error.
throw_UndefinedBuiltin :: String -> QpState a
throw_UndefinedBuiltin n =
  throw_UnboundValue n UndefinedBuiltin


-- | Throw a non-duplicability error, based on the faulty reference flag.
throw_NonDuplicableError :: ConstraintInfo -> QpState a
throw_NonDuplicableError info = do
  p <- pprint_expr_noref $ expression info
  throwQ $ LocatedError (NonDuplicableError p Nothing) (loc info)



-- | Insert a new mapping /x/ |-> /t/ in the substitution, where /x/ is a type variable and /t/ is a linear type.
mapsto :: Variable -> LinType -> QpState ()
mapsto x t = do
  ctx <- get_context
  set_context $ ctx { mappings = IMap.insert x t $ mappings ctx }


-- | Look for a mapping of the argument variable. This function never fails, because if no mapping
-- is found for /x/, the linear type \"x\" is returned.
appmap :: Variable -> QpState LinType
appmap x = do
  ctx <- get_context
  case IMap.lookup x $ mappings ctx of
    Just t -> return t
    Nothing -> return $ TVar x


-- | Recursively apply the mappings recorded in the current state to a linear type.
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

-- The remainging linear types are unit bool qubit and int, and mapped to themselves.
map_lintype typ = do
  return typ


-- | Recursively apply the mappings recorded in the current state to a type.
-- Qubits are intercepted to check the value of their flag.
map_type :: Type -> QpState Type
map_type (TBang f t) = do
  t' <- map_lintype t
  case t' of
    TQubit ->
        unset_flag f no_info
    _ ->
        return ()
  return $ TBang f t'

-- | Recursively apply the mappings recorded in the current state to a
-- type scheme.  Qubits are intercepted to check the value of their
-- flag.
map_typescheme :: TypeScheme -> QpState TypeScheme
map_typescheme (TForall fv ff cset typ) = do
  typ' <- map_type typ
  return $ TForall fv ff cset typ'


-- | Check whether a linear type is a quantum data type or not.
is_qdata_lintype :: LinType -> QpState Bool
is_qdata_lintype TQubit =
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

is_qdata_lintype (TUser typeid args) = do
  spec <- type_spec typeid
  isqdata <- case spec of
               Left def -> return $ d_qdatatype def
               Right syn -> return $ s_qdatatype syn
  if isqdata then
    List.foldl (\rec t -> do
                  b <- rec
                  if b then
                    is_qdata_type t
                  else
                    return False) (return True) args
  else
    return False

is_qdata_lintype _ =
  return False


-- | Check whether a type is a quantum data type or not.
is_qdata_type :: Type -> QpState Bool
is_qdata_type (TBang _ a) =
  is_qdata_lintype a


-- | Complementary printing function for patterns, which
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


-- | Like 'pprint_pattern_noref', but for expressions.
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


-- | A list of names to be used to represent type variables.
available_names :: [String]
available_names = ["a", "b", "c", "d", "a0", "a1", "a2", "b0", "b1", "b2"]


-- | A list of names to be used to represent flag variables.
available_flags :: [String]
available_flags = ["n", "m", "p", "q", "n0", "n1", "n2", "m0", "m1", "m2"]


-- List of pre-defined printing functions

-- | Pre-defined type variable printing function. The variables that may appear in the final type must be given as argument.
-- Each one of these variables is then associated with a name (of the list 'Monad.QpState.available_names').
-- If too few names are given, the remaining variables are displayed as: subvar \'X\' x.
display_var :: [Variable] -> QpState (Variable -> String)
display_var fv = do
  attr <- return $ List.zip fv available_names
  return (\x -> case List.lookup x attr of
                  Just n -> n
                  Nothing -> subvar 'X' x)


-- | Pre-defined flag printing function. It looks up the value of the flags, and display \"!\"
-- if the value is one, and \"\" else.
display_flag :: QpState (RefFlag -> String)
display_flag = do
  refs <- get_context >>= return . flags
  return (\f -> case f of
                  1 -> "!"
                  n | n >= 2 -> case IMap.lookup n refs of
                                  Just FInfo { value = One } -> "!"
                                  Just _ -> ""
                                  Nothing -> ""
                    | otherwise -> "")


-- | Display a reference flag. This function is similar to 'Monad.QpState.display_flag', but
-- displays the reference flag when the value is unknown. The argument gives the reference flags that may appear in the final
-- type. Each reference is then associated with a name.
display_ref :: [RefFlag] -> QpState (RefFlag -> String)
display_ref ff = do
  attr <- return $ List.zip ff available_flags
  refs <- get_context >>= return . flags
  return (\f -> case f of
                  1 -> "!"
                  n | n >= 2 -> case IMap.lookup n refs of
                                  Just FInfo { value = One } -> "!"
                                  Just FInfo { value = Zero } -> ""
                                  _ -> 
                                      case List.lookup n attr of
                                        Just nm -> "(" ++ nm ++ ")"
                                        Nothing -> "(" ++ show n ++ ")"
                    | otherwise -> "")


-- | Re-defined algebraic type printing function. It looks up the name of an algebraic type, or returns
-- subvar \'T\' t if not found.
display_algebraic :: QpState (Variable -> String)
display_algebraic = do
  nspace <- get_context >>= return . namespace
  return (\t -> case IMap.lookup t $ N.typecons nspace of
                  Just n -> n
                  Nothing -> subvar 'T' t)



-- | Type variables are attributed random names before being printed, and the flags are
-- printed with their actual value: only if the flag is set will it be displayed as '!', else it will appear as ''.
pprint_type_noref :: Type -> QpState String
pprint_type_noref t = do
  -- Printing of type variables, flags and types
  fvar <- display_var (free_typ_var t)
  fflag <- display_flag
  fuser <- display_algebraic

  return $ genprint Inf t [fflag, fvar, fuser]



-- | Like 'pprint_type_noref', but for linear types.
pprint_lintype_noref :: LinType -> QpState String
pprint_lintype_noref a = do
  -- Printing of type variables, flags and types
  fvar <- display_var (free_typ_var a)
  fflag <- display_flag
  fuser <- display_algebraic

  return $ genprint Inf a [fflag, fvar, fuser]



-- | Like 'pprint_type_noref', but for typing schemes.
pprint_typescheme_noref :: TypeScheme -> QpState String
pprint_typescheme_noref (TForall ff fv cset typ) = do
  -- Printing of type variables, flags and types
  fvar <- display_var fv
  fflag <- display_flag
  fuser <- display_algebraic

  return $ genprint Inf (TForall ff fv cset typ) [fflag, fvar, fuser]



-- | Like 'pprint_expr_noref', but for values.
pprint_value_noref :: Value -> QpState String
pprint_value_noref v = do
  nspace <- get_context >>= return . namespace
  -- Printing of data constructors
  fdata <- return (\d -> case IMap.lookup d $ N.datacons nspace of
                           Just n -> n
                           Nothing -> subvar 'D' d)

  return $ genprint Inf v [fdata]
