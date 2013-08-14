-- | This module provides a structure that stores the original name of the variables.
-- Each variable, when read by the parser, is registered in this struture, and attributed
-- a unique id at the same time. 

module Monad.Namespace where

import Utils

import Parsing.Localizing

import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap

-- | The definition of the namespace includes two mappings from ids to strings recording the original names, one for
-- term variables, one for data constructors
data Namespace = NSpace {
  varcons :: IntMap String,      -- ^ Stores the variable names.
  varloc :: IntMap Extent,       -- ^ Stores the extent of the variable declaration.
  datacons :: IntMap String,     -- ^ Stores the data constructor names.

  vargen :: Int,                 -- ^ Used to generate new variables ids.
  datagen :: Int                 -- ^ Used to generate new datacon ids.
}


-- | Creates a new namespace, with the counters initialized to zero, and the consing maps empty.
new_namespace :: Namespace
new_namespace = NSpace {
  varcons = IMap.empty,
  datacons = IMap.empty,
  varloc = IMap.empty,

  vargen = 0,
  datagen = 0
}


-- | Registers a new variable, and returns the attributed variable id.
register_var :: String -> Extent -> Namespace -> (Int, Namespace)
register_var s ex namespace =
  let id = vargen namespace in
  (id, namespace { varcons = IMap.insert id s $ varcons namespace,
                   varloc = IMap.insert id ex $ varloc namespace,
                   vargen = id+1 })


-- | Creates a dummy variable: it chooses a fresh id n, and registers it under the name x_n.
dummy_var :: Namespace -> (Int, Namespace)
dummy_var namespace =
  let id = vargen namespace in
  (id, namespace { varcons = IMap.insert id (subvar 'x' id) $ varcons namespace, vargen = id+1 })


-- | Registers a new data constructor, and returns the attributed id.
register_datacon :: String -> Namespace -> (Int, Namespace)
register_datacon s namespace =
  let id = datagen namespace in
  (id, namespace { datacons = IMap.insert id s $ datacons namespace, datagen = id+1 })
