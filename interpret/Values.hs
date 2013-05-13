{- This module defines the data type of values, which will be used
   by the interpreter
-}

module Values where

import Localizing

import Syntax
import Circuits

import Data.Map as Map

-- Type declaration of values
data Value =
    VFun Context Pattern Expr
  | VPair Value Value
  | VCirc Value Circuit Value
  | VBool Bool
  | VBox Type
  | VUnbox Value
  | VUnit
  | VRev
  | VQBit Int     -- Quantum addresses

instance Show Value where
  show (VQBit q) = show q
  show (VPair v1 v2) = "<" ++ show v1 ++ ", " ++ show v2 ++ ">"
  show (VCirc _ c _) = pprintCircuit c
  show (VBool True) = "true"
  show (VBool False) = "false"
  show VUnit = "<>"

-- Definition of the context

-- The context keeps track of :
  -- The current extent - for debug purposes
  -- The current bindings
  -- The circuit being constructed
  -- Available quantum addresses

data Context =
  Ctx {
    -- Localization (extent of the current expression/type/pattern)
    extent :: Extent,

    -- Variable bindings
    bindings :: Map String Value,

    -- Current circuit
    circuit :: Circuit,

    -- For quantum id generation
    qId :: Int
  }

-- Definition of a empty context :
emptyContext :: Context
---------------------
emptyContext =
  Ctx {
    extent = extentUnknown,
    bindings = empty,
    circuit = Circ { qIn = [], qOut = [], gates = [] },
    qId = 0
  }

-- Result of a computation : either the computation succeeded, or it failed at some extent
data Computed a = Ok a | Failed String Extent
newtype State a = State (Context -> (Context, Computed a))
instance Monad State where
  return a = State (\ctx -> (ctx, Ok a))
  fail s = State (\ctx -> (ctx, Failed s $ extent ctx))
  State run >>= action =
    State (\ctx -> let (ctx', a) = run ctx in
                   case a of
                   Ok a ->
                       let State run' = action a in
                       run' ctx'
                   Failed s ex ->
                       (ctx', Failed s ex))

-- Context manipulation --

-- Whole
getContext :: State Context
putContext :: Context -> State ()       -- Note : only the bindings ar modified
swapContext :: Context -> State Context -- Note : the circuit is left unchanged, all other attribute are swapped

-- Extent
getExtent :: State Extent
setExtent :: Extent -> State ()

-- Bindings
insert :: String -> Value -> State ()
find :: String -> State (Maybe Value)
delete :: String -> State ()

-- Circuit construction
unencap :: Circuit -> Binding -> State Binding
openBox :: [Int] -> State Circuit     -- Note : from a list of addresses, open a new circuit, while the old one is returned
closeBox :: Circuit -> State Circuit  -- Note : put the old circuit back in place and return the new one

-- Fresh id generation
newId :: State Int
-------------------------
getContext = State (\ctx -> (ctx, Ok ctx))
putContext ctx = State (\ctx' -> (ctx { circuit = circuit ctx' }, Ok ()))
swapContext ctx = State (\ctx' -> (ctx { circuit = circuit $ ctx' }, Ok ctx'))

getExtent = State (\ctx -> (ctx, Ok $ extent ctx))
setExtent ext = State (\ctx -> (ctx { extent = ext }, Ok ()))

insert x v = State (\ctx -> (ctx { bindings = Map.insert x v $ bindings ctx }, Ok ()))
find x = State (\ctx -> (ctx, Ok $ Map.lookup x $ bindings ctx))
delete x = State (\ctx -> (ctx { bindings = Map.delete x $ bindings ctx }, Ok ()))

unencap c b = State (\ctx -> let (c', b') = Circuits.unencap (circuit ctx) c b in
                             (ctx { circuit = c' }, Ok b'))
openBox ql = State (\ctx -> (ctx { circuit = Circ { qIn = ql, gates = [], qOut = ql } }, Ok $ circuit ctx))
closeBox c = State (\ctx -> (ctx { circuit = c }, Ok $ circuit ctx))

newId = State (\ctx -> (ctx { qId = (+1) $ qId ctx }, Ok $ qId ctx))

