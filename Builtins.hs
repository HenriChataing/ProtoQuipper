-- | This module contains the definition of the built-in operations that are made available to Proto-Quipper
-- code. This includes all the basic gates and some integer operations and comparisons.
module Builtins where

import Parsing.Syntax

import Interpret.Circuits
import Interpret.Values

import Data.Map as Map
import Data.List as List


-- | The type of all unary gates, i.e., @circ (qubit, qubit)@.
unary_type :: Type
unary_type = TCirc TQubit TQubit


-- | The type of all binary gates, i.e., @circ (qubit * qubit, qubit * qubit)@.
binary_type :: Type
binary_type = TCirc (TTensor [TQubit, TQubit]) (TTensor [TQubit, TQubit])


-- | Generic value of unary gates, parameterized over the name of the gate.
-- They are all of the form:
--
-- @
--        ___
--   0 --| N |-- 0
--        ---
-- @
--
-- where /N/ is the name of the gate.
unary_value :: String -> Value
unary_value g =
  VCirc (VQubit 0) (Circ { qIn = [0], gates = [ Unary g 0 ], qOut = [0] }) (VQubit 0) 


-- | Generic value of binary gates, parameterized over the name of the gate.
-- All the binary gate values follow the pattern:
--
-- @
--       ___
--  0 --| N |-- 0
--  1 --|   |-- 1
--       ---
-- @
--
-- where /N/ is the name of the gate.
binary_value :: String -> Value
binary_value g =
  VCirc (VTuple [VQubit 0, VQubit 1])
        (Circ { qIn = [0, 1], gates = [ Binary g 0 1 ], qOut = [0, 1] })
        (VTuple [VQubit 0, VQubit 1])


-- | Subset of the built-in values that provides the definitions of the gates.
-- Below is the exact list of all the defined gates, given by their reference label.
--
-- * The unary gates are : INIT0, INIT1, TERM0, TERM1, PHASE, GATE_H, NOT, GATE_X, GATE_Y, GATE_Z, GATE_S, GATE_S_INV, GATE_T, GATE_T_INV,
--                         GATE_E, GATE_E_INV, GATE_OMEGA, GATE_V, GATE_V_INV.
--
-- * The binary gates are : CNOT, SWAP, CONTROL_PHASE, GATE_W.
--
-- * One ternary gate is defined: TOFFOLI.
--
-- Note that the list of unary and binary gates is actually provided by the "Interpret.Circuits" module.
builtin_gates :: Map String (Type, Value)
builtin_gates =
  let init = [("INIT0", (TCirc TUnit TQubit,
                         VCirc VUnit (Circ { qIn = [], gates = [ Init 0 0 ], qOut = [0] }) (VQubit 0))),
              ("INIT1", (TCirc TUnit TQubit,
                         VCirc VUnit (Circ { qIn = [], gates = [ Init 1 0 ], qOut = [0] }) (VQubit 0)))] in

  let term = [("TERM0", (TCirc TQubit TUnit,
                         VCirc (VQubit 0) (Circ { qIn = [0], gates = [ Term 0 0 ], qOut = [] }) VUnit)),
              ("TERM1", (TCirc TQubit TUnit,
                         VCirc (VQubit 0) (Circ { qIn = [0], gates = [ Term 1 0 ], qOut = [] }) VUnit))] in

  let phase = [("PHASE", (TArrow TInt unary_type,
                          VBuiltin (\(VInt n) -> VCirc (VQubit 0)
                                                       (Circ { qIn = [0], gates = [ Phase n 0 ], qOut = [0] })
                                                       (VQubit 0)))),
               ("CONTROL_PHASE", (TArrow TInt binary_type,
                                  VBuiltin (\(VInt n) -> VCirc (VTuple [VQubit 0, VQubit 1])
                                                               (Circ { qIn = [0, 1], gates = [ Controlled (Phase n 0) [(1,True)] ], qOut = [0, 1] })
                                                               (VTuple [VQubit 0, VQubit 1])))) ] in

  let ceitz = [("CONTROL_GATE_EITZ", (binary_type,
                                  VCirc (VTuple [VQubit 0, VQubit 1])
                                            (Circ { qIn = [0, 1], gates = [ Controlled (Unary "GATE_EITZ" 0) [(1,True)] ], qOut = [0, 1] })
                                            (VTuple [VQubit 0, VQubit 1]))) ] in

  let unary = List.map (\(g, _) -> (g, (unary_type, unary_value g))) unary_gates in
  let binary = List.map (\(g, _) -> (g, (binary_type, binary_value g))) binary_gates in

  let toffoli = ("TOFFOLI", (TCirc (TTensor [TQubit, TQubit, TQubit]) (TTensor [TQubit, TQubit, TQubit]),
                             VCirc (VTuple [VQubit 0, VQubit 1, VQubit 2])
                                   (Circ { qIn = [0, 1, 2], gates = [ Controlled (Unary "NOT" 0) [(1,True), (2,True)] ], qOut = [0, 1, 2] })
                                   (VTuple [VQubit 0, VQubit 1, VQubit 2]))) in

  Map.fromList (toffoli:(init ++ term ++ unary ++ phase ++ ceitz ++ binary))





-- | Subset of the built-in values that provides the definition of the built-in integer operations.
-- The list of currently defined operations is: ADD, SUB, MUL, DIV, MOD, POW, LE, GE, LT, GT, EQ, NE. It is bound to be extended, for
-- example with more comparisons.
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
              ("MOD", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VInt (m `rem` n))))),
              ("POW", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VInt (m ^ n))))),
              ("LE", (TArrow TInt (TArrow TInt TBool),
                      VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VBool (m <= n))))),
              ("GE", (TArrow TInt (TArrow TInt TBool),
                      VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VBool (m >= n))))),
              ("LT", (TArrow TInt (TArrow TInt TBool),
                      VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VBool (m < n))))),
              ("GT", (TArrow TInt (TArrow TInt TBool),
                      VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VBool (m > n))))),
              ("EQ", (TArrow TInt (TArrow TInt TBool),
                      VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VBool (m == n))))), 
              ("NE", (TArrow TInt (TArrow TInt TBool),
                      VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VBool (m /= n)))))
            ] in
  Map.fromList ops

