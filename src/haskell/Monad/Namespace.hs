-- | This module provides a data structure for storing the original name of variables, data constructors and algebraic types.
-- Each variable (resp. data constructor or algebraic type), when read by the parser, is registered in this structure and given a unique id.

module Monad.Namespace (
  Namespace (..),
  empty,

  registerVariable,
  createVariable
  --register_datacon,
  --register_type,

) where

import Utils

import Parsing.Location

import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap
import Data.Map (Map)
import qualified Data.Map as Map

-- | Information relative to a variable.
data VariableInfo = VariableInfo {
  name :: String,
  moduleName :: String  -- ^ Source module (empty if not relevant).
}

-- | The type of name spaces. A namespace includes three mappings from ids to strings, recording the
-- original names. In the case of variables, a reference is recorded that keeps informaton about the
-- type and place of declaration.
data Namespace = Namespace {
  variables :: IntMap VariableInfo,    -- ^ Stores the variable names.

  varref :: IntMap Int,          -- ^ Stores the variable references.

  --datacons :: IntMap String,     -- ^ Stores the data constructor names.
  typecons :: IntMap String,     -- ^ Stores the type names.

  vargen :: Int,                 -- ^ Used to generate new variables ids.
  --datagen :: Int,                -- ^ Used to generate new datacon ids.
  typegen :: Int,                -- ^ Used to generate new type ids.
  -- | Used for variable name generation: attributes a counter to each used string prefix.
  prefix :: Map String Int
}


-- | Create a new namespace, with the counters initialized to zero and all the mappings empty.
empty :: Namespace
empty = Namespace {
  variables = IMap.empty,
  --datacons = IMap.empty,
  typecons = IMap.empty,
  varref = IMap.empty,

  vargen = 0,
  --datagen = 0,
  typegen = 0,

  prefix = Map.empty
}


-- | Register a new variable (with an optional module), and return a newly assigned variable id.
registerVariable :: Maybe String -> String -> Namespace -> (Int, Namespace)
registerVariable moduleName name namespace =
  let id = vargen namespace in
  let info =
        case moduleName of
          Nothing -> VariableInfo { name = name, moduleName = "" }
          Just moduleName -> VariableInfo { name = name, moduleName = moduleName }
        in
  (id, namespace { variables = IMap.insert id info $ variables namespace, vargen = id+1 })


-- | Create a new variable. If the name provided already exists, a number is appended to differenciate
-- it from the previous ones.
createVariable :: String -> Namespace -> (Int, Namespace)
createVariable name namespace =
  let id = vargen namespace in
  case Map.lookup name $ prefix namespace of
    Just n ->
      let info = VariableInfo { name = prevar name n, moduleName = "" } in
      (id, namespace {
            variables = IMap.insert id info $ variables namespace,
            vargen = id+1, prefix = Map.insert name (n+1) $ prefix namespace
          })
    Nothing ->
      let info = VariableInfo { name = prevar name 0, moduleName = "" } in
      (id, namespace {
            variables = IMap.insert id info $ variables namespace,
            vargen = id+1,
            prefix = Map.insert name 1 $ prefix namespace
          })


---- | Register a new data constructor, and return a newly assigned id.
--register_datacon :: String -> Namespace -> (Int, Namespace)
--register_datacon s namespace =
--  let id = datagen namespace in
--  (id, namespace {
--        datacons = IMap.insert id s $ datacons namespace,
--        datagen = id+1 })


---- | Register a new type, and return the newly assigned id.
--register_type :: String -> Namespace -> (Int, Namespace)
--register_type t namespace =
--  let id = typegen namespace in
--  (id, namespace {
--        typecons = IMap.insert id t $ typecons namespace,
--        typegen = id+1 })

