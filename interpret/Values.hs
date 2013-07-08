{- This module defines the data type of values, which will be used
   by the interpreter
-}

module Values where

import Localizing
import Utils
import QuipperError

import CoreSyntax
import Printer
import QpState

import Classes
import Circuits
import Gates
import TransSyntax

import Control.Exception

import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List

-- Type declaration of values
data Value =
    VFun (IntMap Value) Pattern Expr
  | VPair Value Value
  | VCirc Value Circuit Value
  | VBool Bool
  | VBox Type
  | VUnbox
  | VUnboxed Value -- application of unbox to a circuit
  | VUnit
  | VInjL Value
  | VInjR Value
  | VRev
  | VQbit Int     -- Quantum addresses
  deriving Show

instance PPrint Value where
  pprint (VQbit q) = subscript ("q" ++ show q)
  pprint (VPair u v) = "<" ++ pprint u ++ ", " ++ pprint v ++ ">"
  pprint (VCirc _ c _) = pprint c
  pprint (VFun _ p e) = "fun " ++ pprint p ++ " -> " ++ pprint e
  pprint (VInjL e) = "injl(" ++ pprint e ++ ")"
  pprint (VInjR e) = "injr(" ++ pprint e ++ ")"
  pprint (VBool b) = if b then "true" else "false"
  pprint VUnit = "<>"
  pprint VRev = "rev"
  pprint VUnbox = "unbox"
  pprint (VUnboxed c) = "unbox (" ++ pprint c ++ ")"

  sprint v = pprint v
  sprintn _ v = pprint v

-- Associate values to gates
gate_values :: QpState [(Int, Value)]
-------------------------------------
gate_values = do
  linit0 <- find_name "INIT0"
  linit1 <- find_name "INIT1"
  init_values <- return [(linit0, VCirc VUnit (Circ { qIn = [], gates = [ Init 0 0 ], qOut = [0] }) (VQbit 0)),
                         (linit1, VCirc VUnit (Circ { qIn = [], gates = [ Init 0 1 ], qOut = [0] }) (VQbit 0)) ]

  lterm0 <- find_name "TERM0"
  lterm1 <- find_name "TERM1"
  term_values <- return [(lterm0, VCirc (VQbit 0) (Circ { qIn = [], gates = [ Term 0 0 ], qOut = [0] }) VUnit),
                         (lterm1, VCirc (VQbit 0) (Circ { qIn = [], gates = [ Term 0 1 ], qOut = [0] }) VUnit) ]

  unary_values <- List.foldl (\rec s -> do
                                r <- rec
                                lbl <- find_name s
                                g <- return (lbl, VCirc (VQbit 0) (Circ { qIn = [0], gates = [ Unary s 0 ], qOut = [0] }) (VQbit 0))
                                return (g:r)) (return []) unary_gates

  binary_values <- List.foldl (\rec s -> do
                                 r <- rec
                                 lbl <- find_name s
                                 g <- return (lbl, VCirc (VPair (VQbit 0) (VQbit 1))
                                                         (Circ { qIn = [0, 1], gates = [ Binary s 0 1 ], qOut = [0, 1] })
                                                         (VPair (VQbit 0) (VQbit 1)))
                                 return (g:r)) (return []) binary_gates

  return $ init_values ++ term_values ++ unary_values ++ binary_values


-- Context manipulation --

-- Circuit construction
unencap :: Circuit -> Binding -> QpState Binding
open_box :: [Int] -> QpState Circuit     -- Note : from a list of addresses, open a new circuit, while the old one is returned
close_box :: Circuit -> QpState Circuit  -- Note : put the old circuit back in place and return the new one

-- Fresh id generation
new_id :: QpState Int
-------------------------
unencap c b = QpState (\ctx -> let (c', b') = Circuits.unencap (circuit ctx) c b in
                             return (ctx { circuit = c' }, b'))
open_box ql = QpState (\ctx -> return (ctx { circuit = Circ { qIn = ql, gates = [], qOut = ql } }, circuit ctx))
close_box c = QpState (\ctx -> return (ctx { circuit = c }, circuit ctx))

new_id = QpState (\ctx -> return (ctx { qbit_id = (+1) $ qbit_id ctx }, qbit_id ctx))

