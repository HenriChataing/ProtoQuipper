-- | This module describe a data structure used to represent modules internally, as opposed to the type
-- 'Parsing.Syntax.Program' that describes modules as parsed by the parser.
module Monad.Modules where

import Typing.CoreSyntax
import Interpret.Values

import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap


-- | Internal representation of a module. It results from the processing
-- of a module implementation.
data Module = Mod {
  -- Module name, and path to code file
  module_name :: String,             -- ^ Module name.
  filepath :: FilePath,              -- ^ Path to implementation file (no path to interface file).

  -- Module dependencies
  dependencies :: [String],          -- ^ List of module dependencies.

  -- Specifications of the module types
  typespecs :: Map String Typespec,  -- ^ List of the type definitions.

  -- Ids of the global variables
  global_ids :: Map String Variable, -- ^ List of the global variables (the global variables are declared
                                     -- by toplevel declarations, and must appear in the interface file if one
                                     -- is provided).

  -- Types of the global variables
  global_types :: IntMap Type,       -- ^ Types of the global variables.

  -- Global variables definitions
  global_vars :: IntMap Value        -- ^ Values of the global variables.
}


-- | Dummy module.
dummy_module :: Module
dummy_module = Mod {
  module_name = "Dummy",
  filepath = "*UKNOWN*",

  dependencies = [],

  typespecs = Map.empty,

  global_ids = Map.empty,
  global_types = IMap.empty,
  global_vars = IMap.empty
}
