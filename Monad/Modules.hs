-- | This module describes a data structure used to represent modules internally, as opposed to the type
-- 'Parsing.Syntax.Program' that describes modules as parsed by the parser.
module Monad.Modules (
  Module (..),
  empty_module
) where

import Parsing.Location

import Typing.CoreSyntax
import Interpret.Values

import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap


-- | Internal representation of a module. It results from processing
-- a module implementation.
data Module = Mod {
  variables :: Map String Variable,        -- ^ The module's global variables (the ones acessible outside the module).
  datacons :: Map String Datacon,          -- ^ The module's data constructors.
  types :: Map String Int,                 -- ^ The module's algebraic types and type synonyms.
  body :: Maybe Expr                       -- ^ The body of the module. This attribute is filled only when the compilation has been requested.
}


-- | A dummy module.
empty_module :: Module
empty_module = Mod {
  variables = Map.empty,
  datacons = Map.empty,
  types = Map.empty,
  body = Nothing
}
