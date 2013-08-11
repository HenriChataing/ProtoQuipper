-- | This module contains the definition of some built-in operations that are made available in quipper
-- codes. This includes all the basic gates, listed below ; and some integers operations and comparisons.
module Builtins where

import Parsing.Syntax

import Interpret.Circuits
import Interpret.Values

import Data.Map as Map
import Data.List as List


-- | Type of all the unary gates: i.e circ (qbit, qbit).
unary_type :: Type
unary_type = TCirc TQbit TQbit


-- | Type of all the binary gates: i.e circ (qbit * qbit, qbit * qbit).
binary_type :: Type
binary_type = TCirc (TTensor [TQbit, TQbit]) (TTensor [TQbit, TQbit])


-- | Generic value of unary gates, parametrized over the name of the gate.
unary_value :: String -> Value
unary_value g =
  VCirc (VQbit 0) (Circ { qIn = [0], gates = [ Unary g 0 ], qOut = [0] }) (VQbit 0) 


-- | Generic value of binary gates, parametrized over the name of the gate.
binary_value :: String -> Value
binary_value g =
  VCirc (VTuple [VQbit 0, VQbit 1])
        (Circ { qIn = [0, 1], gates = [ Binary g 0 1 ], qOut = [0, 1] })
        (VTuple [VQbit 0, VQbit 1])


-- | Map of the built-in gates.
-- Unary gates are : INIT0, INIT1, TERM0, TERM1, PHASE, GATE_H, NOT, GATE_X, GATE_Y, GATE_Z, GATE_S, GATE_S_INV, GATE_T, GATE_T_INV,
-- GATE_E, GATE_E_INV, GATE_OMEGA, GATE_V, GATE_V_INV.
-- Binary gates are : CNOT, SWAP, CONTROL_PHASE, GATE_W.
-- Trinary gates are : TOFFOLI.
builtin_gates :: Map String (Type, Value)
builtin_gates =
  let init = [("INIT0", (TCirc TUnit TQbit,
                         VCirc VUnit (Circ { qIn = [], gates = [ Init 0 0 ], qOut = [0] }) (VQbit 0))),
              ("INIT1", (TCirc TUnit TQbit,
                         VCirc VUnit (Circ { qIn = [], gates = [ Init 0 1 ], qOut = [0] }) (VQbit 0)))] in

  let term = [("TERM0", (TCirc TQbit TUnit,
                         VCirc (VQbit 0) (Circ { qIn = [], gates = [ Term 0 0 ], qOut = [0] }) VUnit)),
              ("TERM1", (TCirc TQbit TUnit,
                         VCirc (VQbit 0) (Circ { qIn = [], gates = [ Term 0 1 ], qOut = [0] }) VUnit))] in

  let phase = [("PHASE", (TArrow TInt unary_type,
                          VBuiltin (\(VInt n) -> VCirc (VQbit 0)
                                                       (Circ { qIn = [0], gates = [ Phase n 0 ], qOut = [0] })
                                                       (VQbit 0)))),
               ("CONTROL_PHASE", (TArrow TInt binary_type,
                                  VBuiltin (\(VInt n) -> VCirc (VTuple [VQbit 0, VQbit 1])
                                                               (Circ { qIn = [0, 1], gates = [ Controlled (Phase n 0) [1] ], qOut = [0, 1] })
                                                               (VTuple [VQbit 0, VQbit 1])))) ] in

  let unary = List.map (\(g, _) -> (g, (unary_type, unary_value g))) unary_gates in
  let binary = List.map (\(g, _) -> (g, (binary_type, binary_value g))) binary_gates in

  let toffoli = ("TOFFOLI", (TCirc (TTensor [TQbit, TQbit, TQbit]) (TTensor [TQbit, TQbit, TQbit]),
                             VCirc (VTuple [VQbit 0, VQbit 1, VQbit 2])
                                   (Circ { qIn = [0, 1, 2], gates = [ Controlled (Unary "NOT" 0) [1, 2] ], qOut = [0, 1, 2] })
                                   (VTuple [VQbit 0, VQbit 1, VQbit 2]))) in

  Map.fromList (toffoli:(init ++ term ++ unary ++ phase ++ binary))





-- | Map of the built-in operations. This includes the operators : ADD, SUB, MUL, DIV, POW, LT, GT, EQ.
builtin_operations :: Map String (Type, Value)
builtin_operations =
  let ops = [ ("ADD", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VInt (m + n))))),
              ("SUB", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VInt (m - n))))),
              ("MUL", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VInt (m * n))))),
              ("DIV", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VInt (m `quot` n))))),
              ("LT", (TArrow TInt (TArrow TInt TBool),
                      VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VBool (m < n))))),
              ("GT", (TArrow TInt (TArrow TInt TBool),
                      VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VBool (m > n))))),
              ("EQ", (TArrow TInt (TArrow TInt TBool),
                      VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VBool (m == n))))),
              ("POW", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VInt (m ^ n))))) ] in
  Map.fromList ops

