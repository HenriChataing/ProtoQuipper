-- | This module describes a data structure used to represent modules internally, as opposed to the type
-- 'Parsing.Syntax.Program' that describes modules as parsed by the parser.
module Monad.Modules (
  Module (..),
  empty_module
) where

import Parsing.Location

import Typing.CoreSyntax
import Typing.LabellingContext (LabellingContext, empty_label)

import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap

-- | Internal representation of a module. It results from processing
-- a module implementation.
data Module = Mod {
  labelling :: LabellingContext,                 -- ^ A labelling context that contains all the global variables, data constructors and types defined inside the module.
  body :: Maybe Expr                             -- ^ The body of the module. This attribute is filled only when the compilation has been requested.
}


-- | A dummy module.
empty_module :: Module
empty_module = Mod {
  labelling = empty_label,
  body = Nothing
}
