-- | This module contains the definition of labelling contexts, used to respesent the scope of variables,
-- data constructors and types.
module Core.Environment where

import Classes
import Utils

import Core.Syntax

import Data.Map (Map)
import qualified Data.Map as Map


-- | The environment corresponds to the variables, types and data constructors available at one point of
-- the program.
data Environment = Environment {
  variables :: Map String Variable,
  types :: Map String Variable,
  constructors :: Map String Variable
}


-- | Empty environment.
empty :: Environment
empty = Environment {
  variables = Map.empty,
  types = Map.empty,
  constructors = Map.empty
}


instance Context Environment where
  (Environment variables types constructors) <+> (Environment variables' types' constructors') =
    Environment {
      variables = Map.union variables variables',
      types = Map.union types types',
      constructors = Map.union constructors constructors'
    }

  (Environment variables types constructors) \\ (Environment variables' types' constructors') =
    Environment {
      variables = variables Map.\\ variables',
      types = types Map.\\ types',
      constructors = constructors Map.\\ constructors'
    }
