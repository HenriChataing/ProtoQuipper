{- This module defines the data type of values, which will be used
   by the interpreter
-}

module Values where

import Localizing
import Utils

import Syntax
import Printer

import Classes
import Circuits
import Gates

import Data.Map as Map
import Data.List as List

-- Type declaration of values
data Value =
    VFun Context Pattern Expr
  | VPair Value Value
  | VCirc Value Circuit Value
  | VBool Bool
  | VBox Type
  | VUnbox Value
  | VUnit
  | VInjL Value
  | VInjR Value
  | VRev
  | VQBit Int     -- Quantum addresses
  deriving Show

instance PPrint Value where
  pprint (VQBit q) = subscript ("q" ++ show q)
  pprint (VPair u v) = "<" ++ pprint u ++ ", " ++ pprint v ++ ">"
  pprint (VCirc _ c _) = pprint c
  pprint (VFun _ p e) = "fun " ++ pprint p ++ " -> " ++ pprint e
  pprint (VInjL e) = "injl(" ++ pprint e ++ ")"
  pprint (VInjR e) = "injr(" ++ pprint e ++ ")"
  pprint (VBool b) = if b then "true" else "false"
  pprint VUnit = "<>"

  sprint v = pprint v
  sprintn _ v = pprint v

-- Associate values to gates
gate_values :: [(String, Value)]
-------------------------------
gate_values =
  let init_values = [("INIT0", VCirc VUnit (Circ { qIn = [], gates = [ Init 0 0 ], qOut = [0] }) (VQBit 0)),
                    ("INIT1", VCirc VUnit (Circ { qIn = [], gates = [ Init 0 1 ], qOut = [0] }) (VQBit 0)) ] in
  let term_values = [("TERM0", VCirc (VQBit 0) (Circ { qIn = [], gates = [ Term 0 0 ], qOut = [0] }) VUnit),
                    ("TERM1", VCirc (VQBit 0) (Circ { qIn = [], gates = [ Term 0 1 ], qOut = [0] }) VUnit) ] in
  let unary_values = List.map (\s -> (s, VCirc (VQBit 0) (Circ { qIn = [0], gates = [ Unary s 0 ], qOut = [0] }) (VQBit 0))) unary_gates in
  let binary_values = List.map (\s -> (s, VCirc (VPair (VQBit 0) (VQBit 1))
                                               (Circ { qIn = [0, 1], gates = [ Binary s 0 1 ], qOut = [0, 1] })
                                               (VPair (VQBit 0) (VQBit 1)))) binary_gates in

  init_values ++ term_values ++ unary_values ++ binary_values

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
empty_context :: Context
---------------------
empty_context =
  Ctx {
    extent = extent_unknown,
    bindings = empty,
    circuit = Circ { qIn = [], qOut = [], gates = [] },
    qId = 0
  }

instance Show Context where
  show ctx = "%%CLOSURE%%"

{- Monad definition -}

newtype State a = State (Context -> (Context, Computed a))
instance Monad State where
  return a = State (\ctx -> (ctx, Ok a))
  fail s = State (\ctx -> (ctx, Failed (CustomError s $ extent ctx)))
  State run >>= action =
    State (\ctx -> let (ctx', a) = run ctx in
                   case a of
                     Ok a ->
                       let State run' = action a in
                       run' ctx'
                     Failed e ->
                       (ctx', Failed e))

-- Context manipulation --

-- Whole
get_context :: State Context
put_context :: Context -> State ()       -- Note : only the bindings ar modified
swap_context :: Context -> State Context -- Note : the circuit is left unchanged, all other attribute are swapped

-- Extent
get_etxent :: State Extent
set_extent :: Extent -> State ()

-- Bindings
insert :: String -> Value -> State ()
find :: String -> State Value
delete :: String -> State ()

-- Circuit construction
unencap :: Circuit -> Binding -> State Binding
open_box :: [Int] -> State Circuit     -- Note : from a list of addresses, open a new circuit, while the old one is returned
close_box :: Circuit -> State Circuit  -- Note : put the old circuit back in place and return the new one

-- Fresh id generation
new_id :: State Int
-------------------------
get_context = State (\ctx -> (ctx, Ok ctx))
put_context ctx = State (\ctx' -> (ctx { circuit = circuit ctx' }, Ok ()))
swap_context ctx = State (\ctx' -> (ctx { circuit = circuit $ ctx' }, Ok ctx'))

get_etxent = State (\ctx -> (ctx, Ok $ extent ctx))
set_extent ext = State (\ctx -> (ctx { extent = ext }, Ok ()))

insert x v = State (\ctx -> (ctx { bindings = Map.insert x v $ bindings ctx }, Ok ()))
find x = State (\ctx -> (ctx, case Map.lookup x $ bindings ctx of
                                Just v -> Ok v
                                Nothing -> Failed (UnboundVariable x $ extent ctx)))
delete x = State (\ctx -> (ctx { bindings = Map.delete x $ bindings ctx }, Ok ()))

unencap c b = State (\ctx -> let (c', b') = Circuits.unencap (circuit ctx) c b in
                             (ctx { circuit = c' }, Ok b'))
open_box ql = State (\ctx -> (ctx { circuit = Circ { qIn = ql, gates = [], qOut = ql } }, Ok $ circuit ctx))
close_box c = State (\ctx -> (ctx { circuit = c }, Ok $ circuit ctx))

new_id = State (\ctx -> (ctx { qId = (+1) $ qId ctx }, Ok $ qId ctx))

