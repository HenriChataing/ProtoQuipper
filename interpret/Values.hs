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

newtype State a = State (Context -> (Context, a))
instance Monad State where
  return a = State (\ctx -> (ctx, a))
  State run >>= action =
    State (\ctx -> let (ctx', a) = run ctx
                       State run' = action a in
                   run' ctx')

-- Context manipulation --

-- Extent
getExtent :: State Extent
setExtent :: Extent -> State ()
-- Bindings
insert :: String -> Value -> State ()
delete :: String -> State ()
-- Circuit construction
unencap :: Circuit -> Binding -> State Binding
-- Fresh id generation
newId :: State Int
-------------------------
getExtent = State (\ctx -> (ctx, extent ctx))
setExtent ext = State (\ctx -> (ctx { extent = ext }, ()))

insert x v = State (\ctx -> (ctx { bindings = Map.insert x v $ bindings ctx }, ()))
delete x = State (\ctx -> (ctx { bindings = Map.delete x $ bindings ctx }, ()))

unencap c b = State (\ctx -> let (c', b') = Circuits.unencap (circuit ctx) c b in
                             (ctx { circuit = c' }, b'))

newId = State (\ctx -> (ctx { qId = (+1) $ qId ctx }, qId ctx))

--- Various functions for manipulating values, expressions and patterns

-- Generate a fresh qbit id
freshQId :: Context -> (Int, Context)
-------------------------------------
freshQId ctx =
  (qId ctx, ctx { qId = (qId ctx) + 1 })

