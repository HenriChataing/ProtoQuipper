-- | This module defines the state monad that is used throughout the parsing, interpretation, typing, and more
-- generally all the processes working with the core syntax.
module Monad.QpState where

import Utils
import Classes
import Builtins

import Parsing.Location (Extent, extent_unknown, file_unknown)

import Monad.Modules (Module)
import qualified Monad.Modules as M
import Monad.QuipperError hiding (throw)
import qualified Monad.QuipperError as Q (throw, throwNE, throwWE)
import Monad.Namespace (Namespace)
import qualified Monad.Namespace as N

import Typing.CoreSyntax
import Typing.CorePrinter
import Typing.LabellingContext (LabellingContext, LVariable (..))
import qualified Typing.LabellingContext as L

import qualified Compiler.SimplSyntax as C

import Interpret.Circuits hiding (rev)
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
  channel :: Handle,          -- ^ The output channel, by default stdout.
  verbose :: Int,             -- ^ The verbose level, by default nul.
  wall :: Bool                -- ^ Should warnings be turned into errors ?
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


-- | Display a warning. The verbose level is ignored.
write_warning :: Logfile -> Warning -> Maybe Extent -> IO ()
write_warning logfile warn ex = do
  w <- hIsWritable $ channel logfile
  if not w then
    return ()
  else if wall logfile then
    Q.throw warn ex
  else do
    case ex of
      Just ex -> hPutStrLn (channel logfile) $ printE warn ex
      Nothing -> hPutStrLn (channel logfile) $ printE warn extent_unknown
    hFlush (channel logfile)



-- | The different kind of assertions.
data Assertion =
    IsDuplicable
  | IsNonduplicable
  | IsNotfun
  deriving (Show, Eq)


-- | The definition of the QLib module, which contains the definition of all the unbox and box operators.
data QLib = QLib {
  boxes :: Map QType Variable,              -- ^ If the box[T] operator is defined, return the associated variable.
  unboxes :: Map CircType Variable,         -- ^ If the unbox T U operator is defined, return the associated variable.
  rev :: Maybe Variable,                    -- ^ If the rev operator is defined, return the associated variable.
  qbody :: C.Expr                           -- ^ The body of the QLib module.
}


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

data QContext = QCtx {

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
  body :: Maybe (Expr -> Expr),                       -- ^ The (incomplete) body of the current module.

-- Helpers of the typing / interpretation 
  types :: IntMap (Either Typedef Typesyn),           -- ^ The definitions of both the imported types and the types defined in the current module.

  builtins :: Map String (Type, Value),               -- ^ A certain number of predefined and pre-typed functions \/ values are put
                                                      -- in the 'builtins' field, where they are available to both the type checker and the interpreter.
  datacons :: IntMap Datacondef,                      -- ^ Data constructors are considered to be values, and so can be typed individually. This map contains
                                                      -- their type, as written in the type definition.
  globals :: IntMap TypeScheme,                       -- ^ Typing context corresponding to the global variables imported from other modules.

  values :: IntMap Value,                             -- ^ The values of the global variables.

  assertions :: [(Assertion, Type, ConstraintInfo)],  -- ^ A list of assertions, that have to be checked after the type inference. A typical example concerns the pattern matchings, where
                                                      -- function values are prohibited (even type constructors).

-- Information relevant to flags
  flags :: IntMap FlagInfo,                           -- ^ Flags from types are references to this map, which holds information about the value of the flag, but
                                                      -- also about the type itself, for example the expression it is the type of. Such information is useful to send
                                                      -- unambiguous error messages when the type inference fails.

-- Compiler things
  call_conventions :: IntMap [Type],                  -- ^ The calling conventions of the global functions. For now, it specificies the list of extra unbox operator arguments.
                                                      -- (see the function 'Compiler.Preliminaries.disambiguate_unbox_calls' for more information).
  qlib :: QLib,                                       -- ^ The qlib module, from which unbox and box operations are accessed.

-- References
  references :: IntMap RefInfo,                       -- ^ Information about each expression.

-- Circuit stack
  circuits :: [Circuit],                              -- ^ The circuit stack used by the interpreter.

-- Id generation
  type_id :: Int,                                     -- ^ Used to generate fresh type variables.
  flag_id :: Int,                                     -- ^ Used to generate fresh flag references.
  qubit_id :: Int,                                    -- ^ Used to generate fresh quantum addresses. This field can be reinitialized (set to 0) after every new call to box[T].
  ref_id :: Int,                                      -- ^ Used to generate new references.
     
-- Substitution from type variable to types
  mappings :: IntMap LinType                          -- ^ The result of the unification: a mapping from type variables to linear types.
}



-- | The state monad associated with a 'Context'.
-- The monad runs its operations in the 'IO' monad, so it can perform input \/ output operations
-- via a simple lift.
newtype QpState a = QpState { runS :: (QContext -> IO (QContext, a)) }

instance Monad QpState where
  return a = QpState { runS = (\ctx -> return (ctx, a)) }
  fail s = QpState { runS = (\ctx -> Q.throwNE $ ProgramError s) }
  st >>= action = QpState { runS = (\ctx -> do
                                    (ctx', a) <- runS st ctx 
                                    st' <- return $ action a
                                    runS st' ctx') }


-- | Throw an exception of type 'QError' (exceptions specific to Quipper).
throwQ :: QError a => a -> Extent -> QpState b
throwQ e ex =
  QpState { runS = (\ctx -> Q.throwWE e ex) }


-- | Give a warning.
warnQ :: Warning -> Extent -> QpState ()
warnQ w ex = do
  ctx <- get_context
  liftIO $ write_warning (logfile ctx) w $ Just ex


-- | Catch any error thrown in a certain computation, and run a continuation in case
-- an error is caught.
catchQ :: QpState a -> (QuipperError -> QpState a) -> QpState a
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
empty_context :: QContext
empty_context =  QCtx {
-- The logfile is initialized to print on the standard output, with the lowest verbose level possible
  logfile = Logfile { channel = stdout, verbose = 0, wall = False },

-- The namespace is initially empty
  namespace = N.new_namespace,

-- No modules
  modules = [],
  dependencies = [],
  body = Nothing,
 
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

-- No assertions
  assertions = [],

-- No flag
  flags = IMap.empty,

-- no conventions
  call_conventions = IMap.empty,
  qlib = QLib {
    boxes = Map.empty,
    unboxes = Map.empty,
    rev = Nothing,
    qbody = C.EUnit
  },

-- No references
  references = IMap.empty,

-- Circuit stack initialized with a void circuit.
  circuits = [ Circ { qIn = [], gates = [], qOut = [], Interpret.Circuits.qubit_id = 0, unused_ids = [] } ],

  flag_id = 2,   -- Flag ids 0 and 1 are reserved
  type_id = 0,
  Monad.QpState.qubit_id = 0,
  ref_id = 1,
      
  mappings = IMap.empty
}



-- | Return the state context.
get_context :: QpState QContext
get_context = QpState { runS = (\ctx -> return (ctx, ctx)) }


-- | Set the state context.
set_context :: QContext -> QpState ()
set_context ctx = QpState { runS = (\_ -> return (ctx, ())) }


------------------------------------------------
-- ** Log and verbose settings.


-- | Change the level of verbosity.
set_verbose :: Int -> QpState ()
set_verbose v = do
  ctx <- get_context
  set_context $ ctx { logfile = (logfile ctx) { verbose = v } }


-- | Change the processing of warnings.
set_wall :: Bool -> QpState ()
set_wall b = do
  ctx <- get_context
  set_context $ ctx { logfile = (logfile ctx) { wall = b } }



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


------------------------------------------------
-- ** Location settings.


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



------------------------------------------------
-- ** Module settings.


-- | Reinitialize the body.
new_module :: QpState ()
new_module = do
  ctx <- get_context
  set_context ctx { body = Nothing }

-- | Append a declaration at the end of the body.
with_declaration :: (RecFlag, Pattern, Expr) -> QpState ()
with_declaration (r, p, e) = do
  ctx <- get_context
  case body ctx of
    Nothing -> set_context ctx { body = Just (\f -> ELet 0 r p e f) }
    Just cont -> set_context ctx { body = Just (\f -> cont $ ELet 0 r p e f) }

-- | Append an expression at the end of the body.
with_expression :: Expr -> QpState ()
with_expression e =
  with_declaration (Nonrecursive, (PWildcard 0), e)

-- | Return the body of the module, and reinitialize it just after.
module_body :: QpState (Maybe Expr)
module_body = do
  ctx <- get_context
  bdy <- return $ body ctx
  case bdy of
    Nothing -> do
        return Nothing
    Just cont -> do
        bdy <- return $ cont (EUnit 0)
        set_context $ ctx { body = Nothing }
        return $ Just bdy



-- | Register a variable in the namespace. A new id is generated, bound to
-- the given variable, and returned.
register_var :: String -> Ref -> QpState Int
register_var x ref = do
  ctx <- get_context
  (id, nspace) <- return $ N.register_var x ref (namespace ctx)
  set_context $ ctx { namespace = nspace }
  return id


-- | Like 'register_var', but register a data constructor. Note that the variable and data constructor
-- ids may overlap, as they are generated from a different source.
register_datacon :: String -> Datacondef -> QpState Datacon
register_datacon dcon ddef = do
  ctx <- get_context
  (id, nspace) <- return $ N.register_datacon dcon (namespace ctx)
  set_context $ ctx { namespace = nspace,
                      datacons = IMap.insert id ddef $ datacons ctx }
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
        return $ prevar "x" x


-- | Retrieve the reference the vairable was given at ots declaration. 
variable_reference :: Variable -> QpState Ref
variable_reference x = do
  ctx <- get_context
  case IMap.lookup x $ N.varref (namespace ctx) of
    Just ref -> return ref
    Nothing -> return 0


-- | Retrieve the name of the given data constructor. If no match is found in
-- the namespace, produce a standard name /D_n/.
datacon_name :: Variable -> QpState String
datacon_name x = do
  ctx <- get_context
  case IMap.lookup x $ N.datacons (namespace ctx) of
    Just n ->
        return n

    Nothing ->
        return $ prevar "D" x


-- | Retrieve the name of the given type. If no match is found in
-- the namespace, produce a standard name /A_n/.
type_name :: Variable -> QpState String
type_name x = do
  ctx <- get_context
  case IMap.lookup x $ N.typecons (namespace ctx) of
    Just n ->
        return n

    Nothing ->
        return $ prevar "A" x


-- | Create the initializer of the translation into internal syntax. This returns the namespace in which
-- all the global variables and data constructors from the module dependencies have been inserted, associated with their respective
-- inferred type.
global_namespace :: [String]                                                          -- ^ A list of module dependencies.
                 -> QpState LabellingContext                                          -- ^ The resulting labelling maps.
global_namespace deps = do
  mods <- get_context >>= return . modules
  return $ List.foldl (\lctx m ->
        case List.lookup m mods of
          Just mod -> M.labelling mod <+> lctx
          Nothing -> throwNE $ ProgramError $ "QpState:global_namespace: missing implementation of module " ++ m) L.empty_label deps



-- | Look up the type of a global variable.
type_of_global :: Variable -> QpState TypeScheme
type_of_global x = do
  ctx <- get_context
  case IMap.lookup x $ globals ctx of
    Just t ->
        return t
    Nothing -> do
        n <- variable_name x
        fail $ "QpState:type_of_global: undefined global variable " ++ n


-- | Check whether a given variable is global or not.
is_global :: Variable -> QpState Bool
is_global v = do
  ctx <- get_context
  return $ IMap.member v (globals ctx)


-- | Look up a variable in a specific module (typically used with a qualified variable).
-- The input pair is (Module, Var name).
lookup_qualified_var :: (String, String) -> QpState Variable
lookup_qualified_var (mod, n) = do
  ctx <- get_context
  -- Check that the module is part of the M.dependencies
  if List.elem mod $ dependencies ctx then do
    case List.lookup mod $ modules ctx of
      Just modi -> do
          case Map.lookup n $ L.variables $ M.labelling modi of
            Just (LVar x) -> return x
            Just (LGlobal x) -> return x
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
          case Map.lookup n $ L.types $ M.labelling modi of
            Just (TBang _ (TAlgebraic x _)) -> return x
            _ -> do
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
        fail $ "QpState:builtin_type: undefined builtin operation: " ++ s



-- | Look up the value of a built-in object.
builtin_value :: String -> QpState Value
builtin_value s = do
  ctx <- get_context
  case Map.lookup s $ builtins ctx of
    Just (_, v) ->
        return v
    Nothing ->
        fail $ "QpState:builtin_value: undefined builtin operation: " ++ s



-- | Retrieve the definition of a type.
type_spec :: Variable -> QpState (Either Typedef Typesyn)
type_spec typ = do
  ctx <- get_context
  case IMap.lookup typ $ types ctx of
    Just n ->
        return n

    Nothing -> do
        n <- type_name typ
        fail $ "QpState:type_spec: undefined type: " ++ n


-- | Update the definiton of a type.
update_type :: Algebraic -> (Typedef -> Maybe Typedef) -> QpState ()
update_type typ update = do
  ctx <- get_context
  set_context ctx { types = IMap.update (\tdef ->
        case tdef of
          Left def -> (update def) >>= (\x -> return $ Left x)
          Right _ -> throwNE $ ProgramError "QpState:update_type: illegal argument") typ $ types ctx }


-- | Retrieve the definition of a data constructor.
datacon_def :: Datacon -> QpState Datacondef
datacon_def id = do
  ctx <- get_context
  case IMap.lookup id $ datacons ctx of
    Just def ->
        return def
  
    Nothing ->
        -- The sound definition of the data constructors has already been checked
        -- during the translation into the core syntax
        fail $ "QpState:datacon_def: undefined data constructor: " ++ prevar "D" id


-- | Retrieve the reference of the algebraic type of a data constructor.
datacon_datatype :: Datacon -> QpState Variable
datacon_datatype dcon =
  datacon_def dcon >>= return . d_datatype


-- | Retrieve the reference of the algebraic type of a data constructor.
datacon_type :: Datacon -> QpState TypeScheme
datacon_type dcon =
  datacon_def dcon >>= return . d_type


-- | Return the local identifier of a data constructor.
datacon_tag :: Datacon -> QpState Int
datacon_tag dcon =
  datacon_def dcon >>= return . d_tag


-- | Update the definition of a data contructor.
update_datacon :: Datacon -> (Datacondef -> Maybe Datacondef) -> QpState ()
update_datacon dcon update = do
  ctx <- get_context
  set_context ctx { datacons = IMap.update update dcon $ datacons ctx }


-- | Retrieve the list of the data constructors from a type definition.
all_data_constructors :: Variable -> QpState [Datacon]
all_data_constructors typ = do
  Left def <- type_spec typ
  return $ fst $ List.unzip $ snd $ d_unfolded def


-- | Return the list of the constructors' labels of a type definition.
constructors_labels :: Variable -> QpState [Int]
constructors_labels typ = do
  Left def <- type_spec typ
  return $ [0 .. (List.length $ snd $ d_unfolded def) -1]


-- | Add an assertion on a type.
assert :: Assertion -> Type -> ConstraintInfo -> QpState ()
assert ast typ info = do
  ctx <- get_context
  set_context $ ctx { assertions = (ast,typ,info):(assertions ctx) } 


-- | Check the assertions, then remove them. If one assertion is not verified, an error is thrown.
check_assertions :: QpState ()
check_assertions = do
  ctx <- get_context
  -- Successively check all the assertions
  List.foldl (\rec (ast, typ, info) -> do
                rec
                typ' <- map_type typ
                case ast of
                  IsDuplicable -> return ()
                  IsNonduplicable -> return ()
                  IsNotfun ->
                      if not $ is_fun typ' then
                        return ()
                      else
                        fail "QpState:check_assertions: matched value has a function type") (return ()) (assertions ctx)

  set_context $ ctx { assertions = [] }


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
              return $ f_value info

          Nothing ->
              fail $ "QpState:flag_value: undefined flag reference: " ++ prevar "f" ref



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
              case f_value i of
                Zero -> do
                    case c_type info of
                      Just a -> do
                          a0 <- return $ subs_flag ref 0 a
                          a1 <- return $ subs_flag ref 1 a
                          throw_TypingError a0 a1 info { c_actual = True }
                      Nothing ->
                          throw_NonDuplicableError info
                Unknown ->
                    set_context $ ctx { flags = IMap.insert ref (i { f_value = One }) $ flags ctx }
                _ ->
                    return ()  -- Includes anyflag and one

          Nothing ->
              fail $ "QpState:set_flag: undefined flag reference: " ++ prevar "f" ref


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
              case f_value i of
                One ->
                    case c_type info of
                      Just a -> do
                          a0 <- return $ subs_flag ref 0 a
                          a1 <- return $ subs_flag ref 1 a
                          throw_TypingError a0 a1 info { c_actual = False, c_type = Nothing }
                      Nothing ->
                          throw_NonDuplicableError info
                Unknown ->
                    set_context $ ctx { flags = IMap.insert ref (i { f_value = Zero }) $ flags ctx }
                _ ->
                    return ()  -- Includes anyflag and zero

          Nothing ->
              fail $ "QpState:unset_flag: undefined flag reference: " ++ prevar "f" ref


-- | Generate a new flag reference, and add its accompanying binding to the flags map.
-- The flag is initially set to 'Unknown', with no expression or location.
fresh_flag :: QpState RefFlag
fresh_flag = do
  ctx <- get_context
  id <- return $ flag_id ctx
  set_context $ ctx { flag_id = id + 1,
                      flags = IMap.insert id (FInfo { f_value = Unknown }) $ flags ctx }
  return id 


-- | Generate a new flag reference, and add its accompanying binding to the flags map.
-- The new flag is set to the specified value, but it is still un-located.
fresh_flag_with_value :: FlagValue -> QpState RefFlag
fresh_flag_with_value v = do
  ctx <- get_context
  id <- return $ flag_id ctx
  set_context $ ctx { flag_id = id + 1,
                      flags = IMap.insert id (FInfo { f_value = v }) $ flags ctx }
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
              fail $ "QpState:duplicate_flag: undefined flag reference: " ++ prevar "f" ref




-- | Create a new reference, with the current location.
create_ref :: QpState Ref
create_ref = do
  ctx <- get_context
  ex <- get_location
  let id = ref_id ctx
  set_context ctx { ref_id = id + 1, references = IMap.insert id RInfo { r_location = ex,
                                                                         r_expression = Left (EUnit 0),
                                                                         r_type = TBang 0 TUnit } $ references ctx }
  return id


-- | Update the value referenced by the argument.
update_ref :: Ref -> (RefInfo -> Maybe RefInfo) -> QpState ()
update_ref ref f = do
  ctx <- get_context
  set_context ctx { references = IMap.update f ref $ references ctx }


-- | Return the information referenced by the argument, if any is found (else Nothing).
ref_info :: Ref -> QpState (Maybe RefInfo)
ref_info ref = do
  ctx <- get_context
  return $ IMap.lookup ref $ references ctx


-- | Return the information referenced by the argument, and fails if nothing is found.
ref_info_err :: Ref -> QpState RefInfo
ref_info_err ref = do
  ctx <- get_context
  case IMap.lookup ref $ references ctx of
    Nothing -> fail "QpState:ref_info_err: null reference"
    Just ri -> return ri



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

rewrite_flags_in_lintype (TAlgebraic n args) = do
  args' <- List.foldr (\a rec -> do
                         r <- rec
                         a' <- rewrite_flags a
                         return (a':r)) (return []) args
  return (TAlgebraic n args')

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




-- | Return the location and expression of a reference.
ref_expression :: Ref -> QpState (Extent, String)
ref_expression ref = do
  rinfo <- ref_info ref
  case rinfo of
    Just i ->
        case r_expression i of
          Left e -> do
              pe <- pprint_expr_noref e
              return (r_location i, pe)
          Right p -> do
              pp <- pprint_pattern_noref p
              return (r_location i, pp)
    Nothing ->
        return (extent_unknown, "?")


-- | Specify the call convention of a global variable.
set_call_convention :: Variable -> [Type] -> QpState ()
set_call_convention v args = do
  ctx <- get_context
  set_context ctx { call_conventions = IMap.insert v args $ call_conventions ctx }


-- | Return the call convention of the given variable (function), if one is specified, and Nothing else.
call_convention :: Variable -> QpState (Maybe [Type])
call_convention v = do
  ctx <- get_context
  return $ IMap.lookup v $ call_conventions ctx


-- | Profile information.
profile :: QpState ()
profile = do
  ctx <- get_context
  newlog (-2) "############   PROFILE   ############"
  newlog (-2) $ "--- References   : " ++ show (ref_id ctx)
  newlog (-2) $ "--- Flags        : " ++ show (flag_id ctx)
  newlog (-2) $ "--- Types        : " ++ show (type_id ctx)
  newlog (-2) $ "--- Variables    : " ++ show (N.vargen $ namespace ctx)
  newlog (-2) "#####################################"


-- | Throw a typing error, based on the reference flags of the faulty types.
-- The return type can be anything, since an exception will be thrown in any case.
throw_TypingError :: Type -> Type -> ConstraintInfo -> QpState a
throw_TypingError t u info = do
  -- Print the types t and u
  prt <- pprint_type_noref t
  pru <- pprint_type_noref u

  -- Get the location / expression
  let ref = c_ref info
  (ex, expr) <- ref_expression ref 
 
  -- Get the original type
  ori <- case c_type info of
           Just a -> do
               p <- pprint_type_noref a
               return $ Just p
           Nothing ->
               return $ Nothing

  -- Check which of the type is the actual one
  if c_actual info then
    throwQ (DetailedTypingError prt pru ori expr) ex
  else
    throwQ (DetailedTypingError pru prt ori expr) ex



-- | Generic error for unbound values (variables, data constructors, types, builtins).
throw_UnboundValue :: QError a => String -> (String -> a) -> QpState b
throw_UnboundValue v err = do
  ex <- get_location
  throwQ (err v) ex


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
  (ex, expr) <- ref_expression (c_ref info)
  throwQ (NonDuplicableError expr Nothing) ex



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

map_lintype (TAlgebraic typename arg) = do
  arg' <- List.foldr (\a rec -> do
                        r <- rec
                        a' <- map_type a
                        return (a':r)) (return []) arg
  return (TAlgebraic typename arg')

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

is_qdata_lintype (TAlgebraic typeid args) = do
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




-- | A list of names to be used to represent type variables.
available_names :: [String]
available_names = ["a", "b", "c", "d", "a0", "a1", "a2", "b0", "b1", "b2"]


-- | A list of names to be used to represent flag variables.
available_flags :: [String]
available_flags = ["n", "m", "p", "q", "n0", "n1", "n2", "m0", "m1", "m2"]


-- List of pre-defined printing functions

-- | Pre-defined type variable printing function. The variables that may appear in the final type must be given as argument.
-- Each one of these variables is then associated with a name (of the list 'Monad.QpState.available_names').
-- If too few names are given, the remaining variables are displayed as: prevar \'X\' x.
display_typvar :: [Variable] -> QpState (Variable -> String)
display_typvar fv = do
  attr <- return $ List.zip fv available_names
  return (\x -> case List.lookup x attr of
                  Just n -> n
                  Nothing -> prevar "X" x)


-- | Pre-defined variable printing function.
display_var :: QpState (Variable -> String)
display_var = do
  nspace <- get_context >>= return . namespace
  return (\x -> case IMap.lookup x $ N.varcons nspace of
                  Just n -> n
                  Nothing -> prevar "x" x)


-- | Pre-defined flag printing function. It looks up the value of the flags, and display \"!\"
-- if the value is one, and \"\" else.
display_flag :: QpState (RefFlag -> String)
display_flag = do
  refs <- get_context >>= return . flags
  return (\f -> case f of
                  1 -> "!"
                  n | n >= 2 -> case IMap.lookup n refs of
                                  Just FInfo { f_value = One } -> "!"
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
                                  Just FInfo { f_value = One } -> "!"
                                  Just FInfo { f_value = Zero } -> ""
                                  _ -> 
                                      case List.lookup n attr of
                                        Just nm -> "(" ++ nm ++ ")"
                                        Nothing -> "(" ++ show n ++ ")"
                    | otherwise -> "")


-- | Pre-defined algebraic type printing function. It looks up the name of an algebraic type, or returns
-- prevar \'T\' t if not found.
display_algebraic :: QpState (Variable -> String)
display_algebraic = do
  nspace <- get_context >>= return . namespace
  return (\t -> case IMap.lookup t $ N.typecons nspace of
                  Just n -> n
                  Nothing -> prevar "T" t)

-- | Pre-defined data constructor printing function. It looks up the name of a data constructor, or returns
-- prevar \'D\' dcon if not found.
display_datacon :: QpState (Datacon -> String)
display_datacon = do
  nspace <- get_context >>= return . namespace
  return (\d -> case IMap.lookup d $ N.datacons nspace of
                  Just n -> n
                  Nothing -> prevar "D" d)


-- | Complementary printing function for patterns, which
-- replaces the references by their original name.
pprint_pattern_noref :: Pattern -> QpState String
pprint_pattern_noref p = do
  fvar <- display_var
  fdata <- display_datacon
  
  return $ genprint Inf [fvar, fdata] p


-- | Like 'pprint_pattern_noref', but for expressions.
pprint_expr_noref :: Expr -> QpState String
pprint_expr_noref e = do
  fvar <- display_var
  fdata <- display_datacon

  return $ genprint Inf [fvar, fdata] e



-- | Type variables are attributed random names before being printed, and the flags are
-- printed with their actual value: only if the flag is set will it be displayed as '!', else it will appear as ''.
pprint_type_noref :: Type -> QpState String
pprint_type_noref t = do
  -- Printing of type variables, flags and types
  fvar <- display_typvar (free_typ_var t)
  fflag <- display_flag
  fuser <- display_algebraic

  return $ genprint Inf [fflag, fvar, fuser] t



-- | Like 'pprint_type_noref', but for linear types.
pprint_lintype_noref :: LinType -> QpState String
pprint_lintype_noref a = do
  -- Printing of type variables, flags and types
  fvar <- display_typvar (free_typ_var a)
  fflag <- display_flag
  fuser <- display_algebraic

  return $ genprint Inf [fflag, fvar, fuser] a



-- | Like 'pprint_type_noref', but for typing schemes.
pprint_typescheme_noref :: TypeScheme -> QpState String
pprint_typescheme_noref (TForall ff fv cset typ) = do
  -- Printing of type variables, flags and types
  fvar <- display_typvar fv
  fflag <- display_flag
  fuser <- display_algebraic

  return $ genprint Inf [fflag, fvar, fuser] (TForall ff fv cset typ)



-- | Like 'pprint_expr_noref', but for values.
pprint_value_noref :: Value -> QpState String
pprint_value_noref v = do
  -- Printing of data constructors
  fdata <- display_datacon

  return $ genprint Inf [fdata] v



