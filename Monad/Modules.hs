-- | This module describe a data structure used to represent modules internally, as opposed to the type
-- 'Parsing.Syntax.Program' that describes modules as parsed by the parser.
module Monad.Modules where

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
  m_variables :: Map String Variable,        -- ^ The module's variables.

  m_datacons :: Map String Datacon,          -- ^ The module's data constructors.

  m_types :: Map String Int,                 -- ^ The module's types and type synonyms.

  m_body :: Maybe Expr                       -- ^ The body of the module. This attribute is filled only when the compilation has been requested.
}


-- | A dummy module.
dummy_module :: Module
dummy_module = Mod {
  m_variables = Map.empty,
  m_datacons = Map.empty,
  m_types = Map.empty,
  m_body = Nothing
}

