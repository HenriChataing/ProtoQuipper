-- | ProtoQuipper uses a stack of reader monads in order to alleviate the complexity of a unique
-- state moned. The compiler monad supports the generation of circuit code and dummy variables.

module Monad.Compiler where

import Utils
import Parsing.Location

import Language.Constructor

import Monad.Typer as Typer
import Monad.Core (Core)
import Monad.Error hiding (prefix)

import Compiler.SimplSyntax (Declaration (..), Expr, Visibility (..))
import Core.Syntax(Type)

import Control.Monad.Trans
import Control.Monad.Trans.State
import Data.Map as Map
import Data.IntMap as IntMap


-- | The context of implemented quantum operations. If a module uses different instances of the box,
-- unbox, rev operators, their implementation will be placed here until added to the module.
data CircuitLibrary = CircuitLibrary {
  boxes :: Map QuantumType Variable,        -- ^ Store box[T] operator implementations.
  unboxes :: Map CircuitType Variable,      -- ^ Store unbox T U operator implementations.
  rev :: Maybe Variable,                    -- ^ Implementation of the rev operator, if required.
  code :: [Declaration]                     -- ^ Associated declarations.
}

-- | A locale namespace, to be dropped after the compilation. This will be used to generate variables
-- local to the compilation unit.
data LocalNamespace = LocalNamespace {
  vargen :: Int,
  variables :: IntMap String,
  prefix :: Map String Int
}

-- | The compiler state memoizes instantiated quantum operations, for later reuse. It also supports
-- dummy variable generation, independently from the core namespace.
data CompilerState = CompilerState {
  circuitLibrary :: CircuitLibrary,   -- ^ See definition of the type above.
  namespace :: LocalNamespace         -- ^ Local namespace, to be dropped after compilation.

-- call :: IntMap [Type],    -- ^ The calling conventions of the global functions. For now, it
                            -- specificies the list of extra unbox operator arguments. (see the
                            -- function 'Compiler.PatternElimination.disambiguate_unbox_calls' for more
                            -- information).

}

-- | The compiler monad, runs in the typer monad, since type information is required to disambiguate
-- the quantum operators.
type Compiler = StateT CompilerState Typer


-- | Empty circuit library.
emptyLibrary = CircuitLibrary {
    boxes = Map.empty,
    unboxes = Map.empty,
    rev = Nothing,
    code = []
  }

-- | Empty state.
empty :: CompilerState
empty = CompilerState {
    circuitLibrary = emptyLibrary,
    namespace = LocalNamespace {
      vargen = 0, -- Caution : this field should be initialized using the value in the core namespace.
      variables = IntMap.empty,
      prefix = Map.empty
    }
  }


---------------------------------------------------------------------------------------------------
-- * Typer access.

-- | Retrieve a named variable from an (optional) module. An exception is thrown if the variable is
-- not found.
-- TODO : implement.
lookupVariable :: Maybe String -> String -> Compiler Variable
lookupVariable moduleName name =
  createVariable name


---------------------------------------------------------------------------------------------------
-- * Namespace access.

-- | Create a new variable. If the name provided already exists, a number is appended to differenciate
-- it from the previous ones.
createVariable :: String -> Compiler Variable
createVariable name = do
  namespace <- gets namespace
  let id = vargen namespace
  case Map.lookup name $ prefix namespace of
    Just n -> do
      let info = prevar name n
      let newNamespace = namespace {
          variables = IntMap.insert id info $ variables namespace,
          vargen = id+1, prefix = Map.insert name (n+1) $ prefix namespace
        }
      modify (\compiler -> compiler { namespace = newNamespace })
      return id
    Nothing -> do
      let info = prevar name 0
      let newNamespace = namespace {
          variables = IntMap.insert id info $ variables namespace,
          vargen = id+1, prefix = Map.insert name 1 $ prefix namespace
        }
      return id


---------------------------------------------------------------------------------------------------
-- * Circuit library.

-- | Return the circuit library.
getCircuitLibrary :: Compiler CircuitLibrary
getCircuitLibrary = gets circuitLibrary


-- | Bind a new circuit into the library.
bindCircuit :: String -> Expr
            -> (CircuitLibrary -> Variable -> CircuitLibrary)
            -> Compiler Variable
bindCircuit name implementation set = do
  library <- gets circuitLibrary
  binder <- createVariable name
  let declaration = DLet Internal binder implementation
  let newLibrary = set library binder
  modify $ \compiler -> compiler {
    circuitLibrary = newLibrary { code = declaration:(code newLibrary) }
  }
  return binder

-- | Add a new box circuit.
bindBox :: QuantumType -> Expr -> Compiler Variable
bindBox qtyp box =
  bindCircuit "box" box $ \library x ->
    library { boxes = Map.insert qtyp x $ boxes library }

-- | Add a new unbox circuit.
bindUnbox :: (QuantumType, QuantumType) -> Expr -> Compiler Variable
bindUnbox ctyp unbox =
  bindCircuit "unbox" unbox $ \library x ->
    library { unboxes = Map.insert ctyp x $ unboxes library }

-- | Redefine the rev circuit.
bindRev :: Expr -> Compiler Variable
bindRev rev =
  bindCircuit "rev" rev $ \library x -> library { rev = Just x }


-- | Clear the circuit library, returning all the constructed operators.
clearCircuitLibrary :: Compiler [Declaration]
clearCircuitLibrary = do
  library <- gets circuitLibrary
  modify $ \compiler -> compiler { circuitLibrary = emptyLibrary }
  return $ code library


---------------------------------------------------------------------------------------------------
-- * Lifting.

log :: Int -> String -> Compiler ()
log lvl msg = lift $ Typer.log lvl msg

warning :: Warning -> Maybe Extent -> Compiler ()
warning warn ext = lift $ Typer.warning warn ext

runCore :: Core a -> Compiler a
runCore computation = lift $ Typer.runCore computation

runTyper :: Typer a -> Compiler a
runTyper computation = lift computation
