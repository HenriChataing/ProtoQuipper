-- | This module provides a data structure for storing the original name of variables.
-- Each variable, when read by the parser, is registered in this structure, and given
-- a unique id at the same time. 

module Monad.Namespace where

import Utils

import Parsing.Localizing

import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap

-- | The type of name spaces. A name space includes two mappings from ids to strings, recording the original names: one for
-- term variables, one for data constructors.
data Namespace = NSpace {
  varcons :: IntMap String,      -- ^ Stores the variable names.
  varloc :: IntMap Extent,       -- ^ Stores the extent of the variable declaration.
  datacons :: IntMap String,     -- ^ Stores the data constructor names.

  vargen :: Int,                 -- ^ Used to generate new variables ids.
  datagen :: Int                 -- ^ Used to generate new datacon ids.
}


-- | Create a new namespace, with the counters initialized to zero, and all the mappings empty.
new_namespace :: Namespace
new_namespace = NSpace {
  varcons = IMap.empty,
  datacons = IMap.empty,
  varloc = IMap.empty,

  vargen = 0,
  datagen = 0
}


-- | Register a new variable, and return a newly assigned variable id.
register_var :: String -> Extent -> Namespace -> (Int, Namespace)
register_var s ex namespace =
  let id = vargen namespace in
  (id, namespace { varcons = IMap.insert id s $ varcons namespace,
                   varloc = IMap.insert id ex $ varloc namespace,
                   vargen = id+1 })


-- | Create a dummy variable. This chooses a fresh id /n/, and registers it under the name /x_n/.
dummy_var :: Namespace -> (Int, Namespace)
dummy_var namespace =
  let id = vargen namespace in
  (id, namespace { varcons = IMap.insert id (subvar 'x' id) $ varcons namespace, vargen = id+1 })


-- | Register a new data constructor, and return a newly assigned id.
register_datacon :: String -> Namespace -> (Int, Namespace)
register_datacon s namespace =
  let id = datagen namespace in
  (id, namespace { datacons = IMap.insert id s $ datacons namespace, datagen = id+1 })
