-- | This module provides a data structure for storing the original name of variables, data constructors
-- and algebraic types. Each variable (resp. data constructor or algebraic type), when read by the
-- parser, is registered in this structure and given a unique id.

module Core.Namespace (
  Namespace (..),
  empty,

  registerVariable,
  createVariable
) where

import Utils

import Parsing.Location

import Core.Syntax (TypeDefinition)

import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap
import Data.Map (Map)
import qualified Data.Map as Map


-- | Information relative to a variable.
data VariableInfo = VariableInfo {
  variableName :: String,
  variableModule :: String            -- ^ Source module (empty if not relevant).
}

-- | Information relative to a type constructor.
data TypeInfo = TypeInfo {
  typeName :: String,
  typeModule :: String,               -- ^ Source module (empty if not relevant).
  typeDefinition :: TypeDefinition    -- ^ The original type definition (as written in the source).
}

-- | Information relative to a data constructor.
data ConstructorInfo = ConstructorInfo {
  constructorName :: String,
  constructorModule :: String,        -- ^ Source module (empty if not relevant).
  constructorType :: Int              -- ^ Associated type.
}


-- | The type of name spaces. A namespace includes three mappings from ids to strings, recording the
-- original names. In the case of variables, a reference is recorded that keeps informaton about the
-- type and place of declaration.
data Namespace = Namespace {
  variables :: IntMap VariableInfo,           -- ^ Stores the variable names.
  types :: IntMap TypeInfo,                   -- ^ Stores the type information.
  constructors :: IntMap ConstructorInfo,     -- ^ Associated with types: stores data constructors.

  vargen :: Int,                      -- ^ Used to generate new variables ids.
  typegen :: Int,                     -- ^ Used to generate new type ids.
  datagen :: Int,                     -- ^ Used to generate new constructor ids.

  prefix :: Map String Int
}


-- | Create a new namespace, with the counters initialized to zero and all the mappings empty.
empty :: Namespace
empty = Namespace {
  variables = IMap.empty,
  constructors = IMap.empty,
  types = IMap.empty,

  vargen = 0,
  typegen = 0,
  datagen = 0,

  prefix = Map.empty
}


-- | Register a new variable (with an optional module), and return a newly assigned variable id.
registerVariable :: Maybe String -> String -> Namespace -> (Variable, Namespace)
registerVariable moduleName name namespace =
  let id = vargen namespace in
  let info =
        case moduleName of
          Nothing -> VariableInfo name ""
          Just moduleName -> VariableInfo name moduleName
        in
  (id, namespace { variables = IMap.insert id info $ variables namespace, vargen = id+1 })


-- | Create a new variable. If the name provided already exists, a number is appended to differenciate
-- it from the previous ones.
createVariable :: String -> Namespace -> (Variable, Namespace)
createVariable name namespace =
  let id = vargen namespace in
  case Map.lookup name $ prefix namespace of
    Just n ->
      let info = VariableInfo (prevar name n) "" in
      (id, namespace {
            variables = IMap.insert id info $ variables namespace,
            vargen = id+1, prefix = Map.insert name (n+1) $ prefix namespace
          })
    Nothing ->
      let info = VariableInfo (prevar name 0) "" in
      (id, namespace {
            variables = IMap.insert id info $ variables namespace,
            vargen = id+1,
            prefix = Map.insert name 1 $ prefix namespace
          })
