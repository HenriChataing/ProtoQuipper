-- | This module describe a data structure used to represent modules internally.
module Monad.Modules where

import Typing.CoreSyntax
import Interpret.Values

import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap


-- | Internal representation of a module.
data Module = Mod {
  -- Module name, and path to code file
  mname :: String,          -- ^ Module name.
  codefile :: FilePath,     -- ^ Path to implementation file.

  -- Module dependencies
  dependencies :: [String], -- ^ list of module dependencies.

  -- Specifications of the module types
  typespecs :: Map String Typespec,

  -- Ids of the global variables
  global_ids :: Map String Variable,

  -- Types of the global variables
  global_types :: IntMap Type,

  -- Global variables definitions
  global_vars :: IntMap Value
}


-- | Dummy module, never to be used
dummy_module :: Module
dummy_module = Mod {
  mname = "Dummy",
  codefile = "*UKNOWN*",

  dependencies = [],

  typespecs = Map.empty,

  global_ids = Map.empty,
  global_types = IMap.empty,
  global_vars = IMap.empty
}
