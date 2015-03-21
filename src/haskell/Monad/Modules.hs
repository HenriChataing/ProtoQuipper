-- | This module describes a data structure used to represent modules internally, as opposed to the
-- type 'Parsing.Syntax.Program' that describes modules as parsed by the parser.
module Monad.Modules (
  Module (..),
  empty
) where

import Parsing.Location

import Core.Syntax
import Core.Environment (Environment)
import qualified Core.Environment as Environment

import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap

-- | Internal representation of a module. It results from processing a module implementation.
data Module = Module {
  environment :: Environment Int,       -- ^ Environment containing all the global variables, data
                                        -- constructors and types defined inside the module.
  declarations :: [Declaration]         -- ^ The body of the module, which contains the global variable
                                        -- declarations.
}


-- | An empty module.
empty :: Module
empty = Module {
  environment = Environment.empty,
  declarations = []
}
