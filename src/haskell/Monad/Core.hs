-- | ProtoQuipper uses a stack of reader monads in order to alleviate the complexity of a unique
-- state moned. The core monad includes the basic objects that will be used all along the translation.
-- Other monad will be added on top of this one, each adding more possibilities.

module Monad.Core where

import Options hiding (verbose, options)

import Utils
import Parsing.Location

import Language.Constructor (ConstructorInfo)

import Core.Environment
import Core.Namespace as Namespace
import Core.Syntax

import Monad.Error

import Interpret.Values (Value)

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
        Nothing -> lift $ hPutStrLn (channel logfile) $ printE warn extent_unknown
    else if waction == "error" then
      throw warn ex
    else
      return ()
    lift $ hFlush (channel logfile)


---------------------------------------------------------------------------------------------------
-- * Accessors

-- | Return the global options.
getOptions :: Core Options
getOptions = gets options

-- | Return the required module.
require :: String -> Core (Maybe Module)
require name = do
  modules <- gets modules
  return $ List.find (\m -> moduleName m == name) modules


-- | Return the definition of a data constructor.
getConstructorInfo :: Variable -> Core (Maybe ConstructorInfo)
getConstructorInfo constructor =
  gets $ ((IntMap.lookup constructor) . Namespace.constructors) . namespace


---------------------------------------------------------------------------------------------------
-- * Pretty printing.


-- | This type class includes several pretty printing functions, offering some control over the
-- size and form of the display. Four functions are defined, going from the most generic ('genprint')
-- down to the default one ('pprint'), with 'sprintn' and 'sprint' as intermediaries. At least
-- 'genprint' and 'sprintn' must be defined in an instance.
class Printable a where
  -- | The most generic function of the 'PPrint' class.
  genprint :: Lvl           -- ^ The depth limit.
    -> a                    -- ^ The object to print.
    -> Core String          -- ^ The result.

  -- | Less generic than 'genprint'. It is still possible to control the size of the output, but the
  -- rendering of variables and such is fixed.
  sprintn :: Lvl -> a -> Core String

  -- | Same as 'sprintn', but with the default level 2.
  sprint  :: a -> Core String

  -- | Basic printing function. It prints everything, and provides default rendering functions for
  -- the variables. Typically, they will be rendered as /c_n/, where /n/ is the unique id, and /c/
  -- a character that changes depending on the kind of variable (/x/ for term variables, /X/ for type
  -- variables, ! for flag variables, /D/ for data constructors, /A/ for algebraic or synonym types).
  pprint :: a -> Core String

  pprint a = sprintn Inf a
  sprint a = sprintn (Nth 2) a
