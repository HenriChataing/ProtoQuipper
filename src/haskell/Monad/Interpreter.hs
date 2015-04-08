-- | ProtoQuipper uses a stack of reader monads in order to alleviate the complexity of a unique
-- state moned. The interpreter monad supports maintains the valuation map of the evaluated module,
-- and runs the operation on a circuit stack.

module Monad.Interpreter where

import Utils
import Parsing.Location

import Interpreter.Circuits as Circuits
import Interpreter.Values (Value)

import Monad.Core (Core, variableName, require, valuation)
import Monad.Typer as Typer
import Monad.Error

import Control.Monad.Trans
import Control.Monad.Trans.State

import Data.IntMap as IntMap
import Data.List as List (foldl)


-- | The interpreter state runs the circuit stack.
data InterpreterState = InterpreterState {
  qubitgen :: Int,         -- ^ Qubit id generation.
  circuits :: [Circuit],   -- ^ The circuit stack used by the interpreter.
  context :: IntMap Value  -- ^ Values from the imported modules.
}


-- | The interpreter monad, runs in the typer monad.
type Interpreter = StateT InterpreterState Typer


-- | Build the initial interpreter state (by combining the values from the module dependencies).
init :: [String] -> Typer InterpreterState
init dependencies = do
  let state = InterpreterState {
        qubitgen = 0,
        circuits = [],
        context = IntMap.empty
        }
  List.foldl (\rec dep -> do
      state <- rec
      mod <- Typer.runCore $ require dep
      return state { context = IntMap.union (context state) (valuation mod) }
    ) (return state) dependencies


-- | Load the valuation of a module.
load :: String -> Interpreter ()
load name = do
  mod <- Monad.Interpreter.runCore $ require name
  modify $ \state -> state {
      context = IntMap.union (context state) $ valuation mod
    }

---------------------------------------------------------------------------------------------------
-- * Qubit generation.

-- | Generate a fresh quantum address. The index should be reinitialized back to 0 at each box
-- creation. Thus, the inputs of a box will always be numbered 0../n/.
freshQubit :: Interpreter Int
freshQubit = do
  q <- gets qubitgen
  setQubit $ q+1
  return q

-- | Return without modifying it the value of the qubit counter.
lastQubit :: Interpreter Int
lastQubit = gets qubitgen

-- | Reset the counter of qubit values. Since the quantum addresses are bound in a circuit
-- (/t/, /C/, /u/), we can reset the counter for each box creation.
resetQubit :: Interpreter ()
resetQubit = setQubit 0

-- | Set the counter of qubit values.
setQubit :: Int -> Interpreter ()
setQubit q = modify $ \state -> state { qubitgen = q }


---------------------------------------------------------------------------------------------------
-- * Circuit manipulation.

-- | Create a new circuit, initialized with a set of wire identifiers, and put it on top of the
-- circuit stack.
openBox :: [Int] -> Interpreter ()
openBox wires = do
  let circuit = createCircuit wires
  modify $ \state -> state { circuits = circuit:(circuits state) }


-- | Unstack and return the top circuit from the circuit stack.
-- The stack must be non empty. An empty circuit stack causes a runtime error.
closeBox :: Interpreter Circuit
closeBox = do
  stack <- gets circuits
  case stack of
    [] -> fail "Interpreter:closeBox: empty circuit stack"
    (top:rest) -> do
      modify $ \state -> state { circuits = rest }
      return top


-- | Append a circuit, using the specified binding. The action is done on the top circuit. If the
-- circuit list is empty, throw a runtime error. The output of 'unencap' is a binding corresponding
-- to the renaming of the addresses done by the circuit constructor.
unencap :: Circuit -> Binding -> Interpreter Binding
unencap circ map = do
  stack <- gets circuits
  case stack of
    [] -> fail "Interpreter:unencap: empty circuit stack"
    (top:rest) -> do
      let (circ', map') = Circuits.unencap top circ map
      modify $ \state -> state { circuits = (circ':rest) }
      return map'


---------------------------------------------------------------------------------------------------
-- * Context.

-- | Return the value of a global variable.
getValue :: Variable -> Interpreter Value
getValue x = do
  context <- gets context
  case IntMap.lookup x context of
    Just v -> return v
    Nothing -> do
      name <- Monad.Interpreter.runCore $ variableName x
      fail $ "Interpreter:getValue: undefined global variable " ++ name


---------------------------------------------------------------------------------------------------
-- * Lifting.

log :: Int -> String -> Interpreter ()
log lvl msg = lift $ Typer.log lvl msg

warning :: Warning -> Maybe Extent -> Interpreter ()
warning warn ext = lift $ Typer.warning warn ext

runCore :: Core a -> Interpreter a
runCore computation = lift $ Typer.runCore computation

runTyper :: Typer a -> Interpreter a
runTyper computation = lift computation
