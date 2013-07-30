-- | This module provides a structure aimed at variable consing.
-- Specifically, it attributes a unique identification (= Int) to each variable.

module Monad.Namespace where

import Utils

import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap

-- | The definition of the namespace includes two mappings from ids to strings recording the original names, one for
-- term variables, one for data constructors
data Namespace = NSpace {
  varcons :: IntMap String,
  datacons :: IntMap String,

  vargen :: Int,
  datagen :: Int
}


-- | Create a new namespace, with the counter initialized to zero, and the consing map empty
new_namespace :: Namespace
new_namespace = NSpace {
  varcons = IMap.empty,
  datacons = IMap.empty,

  vargen = 0,
  datagen = 0
}


-- | Register a new variable
register_var :: String -> Namespace -> (Int, Namespace)
register_var s namespace =
  let id = vargen namespace in
  (id, namespace { varcons = IMap.insert id s $ varcons namespace, vargen = id+1 })


-- | Create a dummy variable
dummy_var :: Namespace -> (Int, Namespace)
dummy_var namespace =
  let id = vargen namespace in
  (id, namespace { varcons = IMap.insert id (subvar 'x' id) $ varcons namespace, vargen = id+1 })


-- | Register a new data constructor
register_datacon :: String -> Namespace -> (Int, Namespace)
register_datacon s namespace =
  let id = datagen namespace in
  (id, namespace { datacons = IMap.insert id s $ datacons namespace, datagen = id+1 })
