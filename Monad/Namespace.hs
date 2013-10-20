-- | This module provides a data structure for storing the original name of variables, data constructors and algebraic types.
-- Each variable (resp. data constructor or algebraic type), when read by the parser, is registered in this structure and given a unique id.

module Monad.Namespace (
  Namespace (..),
  new_namespace,

  register_var,
  register_datacon,
  register_type,

  dummy_var
) where

import Utils

import Parsing.Location

import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap

-- | The type of name spaces. A namespace includes three mappings from ids to strings, recording the original names.
-- In the case of variables, a reference is recorded that keeps informaton about the type and place of declaration.
data Namespace = NSpace {
  varcons :: IntMap String,      -- ^ Stores the variable names.
  varref :: IntMap Int,          -- ^ Stores the variable references.

  datacons :: IntMap String,     -- ^ Stores the data constructor names.
  typecons :: IntMap String,     -- ^ Stores the type names.

  vargen :: Int,                 -- ^ Used to generate new variables ids.
  datagen :: Int,                -- ^ Used to generate new datacon ids.
  typegen :: Int                 -- ^ Used to generate new type ids.
}


-- | Create a new namespace, with the counters initialized to zero and all the mappings empty.
new_namespace :: Namespace
new_namespace = NSpace {
  varcons = IMap.empty,
  datacons = IMap.empty,
  typecons = IMap.empty,
  varref = IMap.empty,

  vargen = 0,
  datagen = 0,
  typegen = 0
}


-- | Register a new variable, and return a newly assigned variable id.
register_var :: String -> Int -> Namespace -> (Int, Namespace)
register_var s ref namespace =
  let id = vargen namespace in
  (id, namespace {
        varcons = IMap.insert id s $ varcons namespace,
        varref = IMap.insert id ref $ varref namespace,
        vargen = id+1 })


-- | Create a dummy variable. This chooses a fresh id /n/, and registers it under the name /x_n/.
dummy_var :: Namespace -> (Int, Namespace)
dummy_var namespace =
  let id = vargen namespace in
  (id, namespace {
        varcons = IMap.insert id (subvar 'x' id) $ varcons namespace,
        vargen = id+1 })


-- | Register a new data constructor, and return a newly assigned id.
register_datacon :: String -> Namespace -> (Int, Namespace)
register_datacon s namespace =
  let id = datagen namespace in
  (id, namespace {
        datacons = IMap.insert id s $ datacons namespace,
        datagen = id+1 })


-- | Register a new type, and return the newly assigned id.
register_type :: String -> Namespace -> (Int, Namespace)
register_type t namespace =
  let id = typegen namespace in
  (id, namespace {
        typecons = IMap.insert id t $ typecons namespace,
        typegen = id+1 })


