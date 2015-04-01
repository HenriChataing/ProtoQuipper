-- | This module provides a data structure for storing the original name of variables, data constructors
-- and algebraic types. Each variable (resp. data constructor or algebraic type), when read by the
-- parser, is registered in this structure and given a unique id.

module Core.Namespace (
  Namespace (..),
  Core.Namespace.empty,

  setTag,
  setCallingConvention,
  setConstructorFormat,
  changeTypeDefinition,
  registerVariable,
  registerTypeDefinition,
  registerConstructor,
  createVariable,
  freshFlag, freshType
) where

import Utils

import Language.Variable as Variable
import Language.Constructor as Constructor
import Language.Type as Type hiding (constructors)

import Core.Syntax (Type)
import qualified Compiler.SimplSyntax as C (Expr)

import Data.IntMap as IntMap
import Data.Map as Map


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
  flaggen :: Int,                     -- ^ Used to generate new flag ids.

  prefix :: Map String Int
}


-- | Create a new namespace, with the counters initialized to zero and all the mappings empty.
empty :: Namespace
empty = Namespace {
  variables = IntMap.empty,
  constructors = IntMap.empty,
  types = IntMap.empty,

  vargen = 0,
  typegen = 0,
  datagen = 0,
  flaggen = 2,

  prefix = Map.empty
}


-- | Register a new variable (with an optional module), and return a newly assigned variable id.
registerVariable :: Maybe String -> String -> Namespace -> (Variable, Namespace)
registerVariable moduleName name namespace =
  let id = vargen namespace in
  let info =
        case moduleName of
          Nothing -> VariableInfo name "" []
          Just moduleName -> VariableInfo name moduleName []
        in
  (id, namespace { variables = IntMap.insert id info $ variables namespace, vargen = id+1 })


-- | Create a new variable. If the name provided already exists, a number is appended to differenciate
-- it from the previous ones.
createVariable :: String -> Namespace -> (Variable, Namespace)
createVariable name namespace =
  let id = vargen namespace in
  case Map.lookup name $ prefix namespace of
    Just n ->
      let info = VariableInfo (prevar name n) "" [] in
      (id, namespace {
            variables = IntMap.insert id info $ variables namespace,
            vargen = id+1, prefix = Map.insert name (n+1) $ prefix namespace
          })
    Nothing ->
      let info = VariableInfo (prevar name 0) "" [] in
      (id, namespace {
            variables = IntMap.insert id info $ variables namespace,
            vargen = id+1,
            prefix = Map.insert name 1 $ prefix namespace
          })


-- | Register a new type definition (with an optional module), and return a newly assigned type id.
registerTypeDefinition :: TypeInfo -> Namespace -> (Variable, Namespace)
registerTypeDefinition definition namespace =
  let id = typegen namespace in
  (id, namespace { types = IntMap.insert id definition $ types namespace, typegen = id+1 })


-- | Update the definition of a type.
changeTypeDefinition :: Variable -> (TypeInfo -> TypeInfo) -> Namespace -> Namespace
changeTypeDefinition typ change namespace =
  namespace { types = IntMap.adjust change typ $ types namespace }


-- | Register a new data constructor.
registerConstructor :: ConstructorInfo -> Namespace -> (Variable, Namespace)
registerConstructor definition namespace =
  let id = datagen namespace in
  (id, namespace { constructors = IntMap.insert id definition $ constructors namespace, datagen = id+1 })


-- | Set the calling convention for a variable in the namespace.
setCallingConvention :: Variable -> [Type] -> Namespace -> Namespace
setCallingConvention x typs namespace =
  namespace {
    variables = IntMap.adjust (\info ->
        info { callingConvention = typs }
      ) x $ variables namespace }


-- | Specify the constructor's builder and destructor.
setConstructorFormat :: Variable
                    -> (Int -> Either C.Expr (C.Expr -> C.Expr))
                    -> (Variable -> C.Expr)
                    -> Namespace
                    -> Namespace
setConstructorFormat constructor build extract namespace =
  namespace {
    constructors = IntMap.adjust (\info ->
        info { build = build $ Constructor.tag info, extract = extract }
      ) constructor $ constructors namespace
    }


-- | Set the tag accessor of an algebraic type.
setTag :: Variable -> (Variable -> C.Expr) -> Namespace -> Namespace
setTag typ accessor namespace =
  namespace {
    types = IntMap.adjust (\info -> info { Type.tag = accessor }) typ $ types namespace }


-- | Return a fresh flag.
freshFlag :: Namespace -> (Variable, Namespace)
freshFlag namespace =
  let id = flaggen namespace in
  (id, namespace { flaggen = id+1 })

-- | Return a fresh type variable.
freshType :: Namespace -> (Variable, Namespace)
freshType namespace =
  let id = typegen namespace in
  (id, namespace { typegen = id+1 })
