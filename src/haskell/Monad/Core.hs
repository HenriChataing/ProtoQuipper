-- | ProtoQuipper uses a stack of reader monads in order to alleviate the complexity of a unique
-- state moned. The core monad includes the basic objects that will be used all along the translation.
-- Other monad will be added on top of this one, each adding more possibilities.

module Monad.Core where

import Options hiding (verbose, options)

import Utils
import Classes
import Parsing.Location

import Language.Constructor as Constructor
import Language.Variable as Variable
import Language.Type as Type

import Core.Environment
import Core.Namespace (Namespace)
import qualified Core.Namespace as Namespace
import Core.Syntax hiding (sourceType)
import qualified Compiler.SimplSyntax as C

import Monad.Error

import Interpreter.Values (Value)

import System.IO
import Control.Monad.Trans
import Control.Monad.Trans.State
import Data.IntMap as IntMap
import Data.List as List


-- | A data type to implement a logger. Logs can be given different priorities, depending on their
-- importance. Any log whose priority is lower than the verbose control is discarded. The logs are
-- printed to a channel, which can be, for example, 'stdout', 'stderr', or any file writing channel.
data Logfile = Logfile {
  channel :: Handle,          -- ^ The output channel, by default stdout.
  verbose :: Int,             -- ^ The verbose level, by default nul.
  warnings :: String          -- ^ Handling of warnings (error, print, ignore).
}

-- | A precompiled module. Depending on the run options, it may contain the variable namespace, the
-- type map and the values of the toplevel members.
data Module = Module {
  moduleName :: String,       -- ^ The module name.
  filePath :: String,         -- ^ Path to the module implementation.
  environment :: Environment, -- ^ Names of the toplevel variables, types and data constructors.
  typemap :: IntMap Type,     -- ^ Inferred types for each module exported expressions.
  valuation :: IntMap Value   -- ^ (optional) valuation of the toplevel members.
}

-- | The core monad keeps track of module information, and contains all module dependencies.
data CoreState = CoreState {
  logfile :: Logfile,         -- ^ Logging settings.
  options :: Options,         -- ^ Run options.
  modules :: [Module],        -- ^ Compiled modules.
  namespace :: Namespace      -- ^ Global namespace (exported members).
}

type Core = StateT CoreState IO


---------------------------------------------------------------------------------------------------
-- * Logger

-- | Log a message with a given priority level.
log :: Int -> String -> Core ()
log lvl msg = do
  logfile <- gets logfile
  w <- lift $ hIsWritable $ channel logfile
  if lvl >= verbose logfile || not w then
    return ()
  else do
    lift $ hPutStrLn (channel logfile) msg
    lift $ hFlush (channel logfile)


-- | Display a warning. The verbose level is ignored. If the option \'Werror\' was added, all warnings
-- are raised as errors.
warning :: Warning -> Maybe Extent -> Core ()
warning warn ex = do
  logfile <- gets logfile
  w <- lift $ hIsWritable $ channel logfile
  if not w then
    return ()
  else do
    let waction = warnings logfile
    if waction == "display" then
      case ex of
        Just ex -> lift $ hPutStrLn (channel logfile) $ printE warn ex
        Nothing -> lift $ hPutStrLn (channel logfile) $ printE warn unknownExtent
    else if waction == "error" then
      throw warn ex
    else
      return ()
    lift $ hFlush (channel logfile)


---------------------------------------------------------------------------------------------------
-- * Core

-- | Return the global options.
getOptions :: Core Options
getOptions = gets options


-- | Return the required module.
require :: String -> Core (Maybe Module)
require name = do
  modules <- gets modules
  return $ List.find (\m -> moduleName m == name) modules


---------------------------------------------------------------------------------------------------
-- * Variables.

-- | Retrieve the name of the given variable. If no match is found in the namespace, produce a standard
-- name of the form /x_n/.
variableName :: Variable -> Core String
variableName x = do
  namespace <- gets namespace
  case IntMap.lookup x $ Namespace.variables namespace of
    Just info -> return $ Variable.name info
    Nothing -> return $ prevar "x" x


-- | Set the calling convention for a variable in the namespace.
setCallingConvention :: Variable -> [Type] -> Core ()
setCallingConvention x typs =
  modify $ \core -> core { namespace = Namespace.setCallingConvention x typs $ namespace core }


---------------------------------------------------------------------------------------------------
-- * Type implementation.

-- | Return the definition of a type.
getTypeInfo :: Variable -> Core TypeInfo
getTypeInfo typ = do
  info <- gets $ ((IntMap.lookup typ) . Namespace.types) . namespace
  case info of
    Just info -> return info
    Nothing ->
      fail $ "Monad.Core:getTypeInfo: undefined type: " ++ prevar "T" typ


-- | Return the definition of a type.
getTypeDefinition :: Variable -> Core TypeDefinition
getTypeDefinition typ = do
  info <- getTypeInfo typ
  return $ definition info


-- | Return the tag accessor of an algebraic type.
getTag :: Variable -> Variable -> Core C.Expr
getTag typ x = do
  info <- getTypeInfo typ
  return $ Type.tag info x


-- | Set the tag accessor of an algebraic type.
setTag :: Variable -> (Variable -> C.Expr) -> Core ()
setTag typ accessor =
  modify $ \core -> core { namespace = Namespace.setTag typ accessor $ namespace core }


-- | Settle the implementation (machine representation) of all the constructors of an algebraic type.
-- The implementation will depend on the number of constructors and the number of constructors with
-- arguments. This method will decide where the tag should be inserted, as well as the structure of
-- each constructor.
setTypeImplementation :: Variable -> Core ()
setTypeImplementation typ = do
  definition <- getTypeDefinition typ
  case definition of
    -- Synonym type: nothing to do here.
    Synonym _ _ _ -> return ()
    -- Cases with one constructor: The tag is omitted. No definition of the function getTag is needed.
    -- The data is a pointer reference if the constructors takes an argument, the value 0 else.
    Algebraic _ _ [(cons, Just _)] -> setConstructorFormat cons (\_ -> Right id) (\v -> C.EVar v)
    Algebraic _ _ [(cons, Nothing)] -> setConstructorFormat cons (\tag -> Left $ C.int 0) (\v -> C.int 0)
    -- Cases with several constrcutors.
    Algebraic _ _ constructors -> do
      List.foldl (\rec (cons, arg) -> do
          rec
          case arg of
            Just _ ->
              setConstructorFormat cons
                (\tag -> Right $ \e -> C.ETuple [C.int tag, e])
                (\v -> C.EAccess 1 v)
            Nothing ->
              setConstructorFormat cons
                (\tag -> Left $ C.ETuple [C.int tag])
                (\v -> C.int 0)
        ) (return ()) constructors
      -- The tag is the first element of the tuple.
      Monad.Core.setTag typ $ \v -> C.EAccess 0 v


---------------------------------------------------------------------------------------------------
-- * Data constructors.

-- | Return the definition of a data constructor.
getConstructorInfo :: Variable -> Core ConstructorInfo
getConstructorInfo constructor = do
  info <- gets $ ((IntMap.lookup constructor) . Namespace.constructors) . namespace
  case info of
    Just info -> return info
    Nothing ->
      fail $ "Monad.Core:getConstructorInfo: undefined data constructor: " ++ prevar "D" constructor


-- | Specify the constructor's builder and destructor. The builder gets the constructor's tag as
-- additional argument.
setConstructorFormat :: Variable
                    -> (Int -> Either C.Expr (C.Expr -> C.Expr))
                    -> (Variable -> C.Expr)
                    -> Core ()
setConstructorFormat constructor build extract =
  modify $ \core -> core {
      namespace = Namespace.setConstructorFormat constructor build extract $ namespace core
    }


-- | Return the source type of a data constructor.
getConstructorSourceType :: Variable -> Core Variable
getConstructorSourceType constructor = do
  info <- getConstructorInfo constructor
  return $ sourceType info


-- | Return the list of data constructors of a type.
getAllConstructors :: Variable -> Core [Datacon]
getAllConstructors typ = do
  info <- getTypeInfo typ
  case definition info of
    Algebraic _ _ constructors -> return $ List.map fst constructors
    Synonym _ _ _ -> return []


---------------------------------------------------------------------------------------------------
-- * Pretty printing.

-- | Pre-defined variable printing function.
displayVar :: Core (Variable -> String)
displayVar = do
  variables <- gets $ Namespace.variables . namespace
  return $ \x ->
      case IntMap.lookup x variables of
        Just info -> Variable.name info
        Nothing -> prevar "x" x

-- | Pre-defined algebraic type printing function. It looks up the name of an algebraic type, or returns
-- prevar \'T\' t if not found.
displayUserType :: Core (Variable -> String)
displayUserType = do
  types <- gets $ Namespace.types . namespace
  return $ \t ->
      case IntMap.lookup t types of
        Just info -> Type.name info
        Nothing -> prevar "T" t

-- | Pre-defined data constructor printing function. It looks up the name of a data constructor, or returns
-- prevar \'D\' dcon if not found.
displayConstructor :: Core (Datacon -> String)
displayConstructor = do
  constructors <- gets $ Namespace.constructors . namespace
  return $ \d ->
      case IntMap.lookup d constructors of
        Just info -> Constructor.name info
        Nothing -> prevar "D" d


-- | Complementary printing function for patterns, which
-- replaces the references by their original name.
printPattern :: Pattern -> Core String
printPattern pattern = do
  pVar <- displayVar
  pCons <- displayConstructor
  return $ genprint Inf [pVar, pCons] pattern

-- | Like 'printPattern', but for expressions.
printExpr :: Expr -> Core String
printExpr expr = do
  pVar <- displayVar
  pCons <- displayConstructor
  return $ genprint Inf [pVar, pCons] expr

-- | Like 'printExpr', but for values.
printValue :: Value -> Core String
printValue value = do
  pCons <- displayConstructor
  return $ genprint Inf [pCons] value
