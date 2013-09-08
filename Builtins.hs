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
  VCirc (VQubit 0) (Circ {
                      qIn = [0],
                      gates = [ Unary g 0 ],
                      qOut = [0],
                      qubit_id = 1,
                      unused_ids = [] }) (VQubit 0) 


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
        (Circ { qIn = [0, 1],
                gates = [ Binary g 0 1 ],
                qOut = [0, 1],
                qubit_id = 2,
                unused_ids = [] })
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
                         VCirc VUnit (singleton_circuit $ Init 0 0) (VQubit 0))),
              ("INIT1", (TCirc TUnit TQubit,
                         VCirc VUnit (singleton_circuit $ Init 1 0) (VQubit 0)))] in

  let term = [("TERM0", (TCirc TQubit TUnit,
                         VCirc (VQubit 0) (singleton_circuit $ Term 0 0) VUnit)),
              ("TERM1", (TCirc TQubit TUnit,
                         VCirc (VQubit 0) (singleton_circuit $ Term 1 0) VUnit))] in

  let phase = [("PHASE", (TArrow TInt unary_type,
                          VBuiltin (\(VInt n) -> VCirc (VQubit 0) (singleton_circuit $ Phase n 0) (VQubit 0)))),
               ("CONTROL_PHASE", (TArrow TInt (TArrow TBool binary_type),
                                  VBuiltin (\(VInt n) -> 
                                             VBuiltin (\(VBool sign) -> 
                                                        VCirc (VTuple [VQubit 0, VQubit 1])
                                                              (singleton_circuit $ Controlled (Phase n 0) [(1,sign)]) 
                                                              (VTuple [VQubit 0, VQubit 1]))))) ] in

  let ceitz = [("CONTROL_GATE_EITZ", (TArrow TBool binary_type,
                                  VBuiltin (\(VBool sign) ->
                                             VCirc (VTuple [VQubit 0, VQubit 1])
                                                   (singleton_circuit $ Controlled (Unary "GATE_EITZ" 0) [(1,sign)])
                                                   (VTuple [VQubit 0, VQubit 1])))) ] in

  let unary = List.map (\(g, _) -> (g, (unary_type, unary_value g))) unary_gates in
  let binary = List.map (\(g, _) -> (g, (binary_type, binary_value g))) binary_gates in

  let cnot = [("CNOT", (TArrow TBool (TCirc (TTensor [TQubit, TQubit]) (TTensor [TQubit, TQubit])),
                             VBuiltin (\(VBool sign) ->
                                        VCirc (VTuple [VQubit 0, VQubit 1])
                                              (singleton_circuit $ Controlled (Unary "NOT" 0) [(1,sign)])
                                              (VTuple [VQubit 0, VQubit 1])))),
              ("TOFFOLI", (TArrow TBool (TArrow TBool (TCirc (TTensor [TQubit, TQubit, TQubit]) (TTensor [TQubit, TQubit, TQubit]))),
                             VBuiltin (\(VBool sign1) ->
                                        VBuiltin (\(VBool sign2) ->
                                                   VCirc (VTuple [VQubit 0, VQubit 1, VQubit 2])
                                                         (singleton_circuit $ Controlled (Unary "NOT" 0) [(1,sign1),(2,sign2)])
                                                         (VTuple [VQubit 0, VQubit 1, VQubit 2]))))) ] in

  Map.fromList (cnot ++ init ++ term ++ unary ++ phase ++ ceitz ++ binary)





-- | Subset of the built-in values that provides the definition of the built-in integer operations.
-- The list of currently defined operations is: ADD, SUB, MUL, QUOT, REM, DIV, MOD, POW, LE, GE, LT, GT, EQ, NE. It is bound to be extended, for
-- example with more comparisons.
builtin_operations :: Map String (Type, Value)
builtin_operations =
  let ops = [ ("ADD", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VInt (m + n))))),
              ("SUB", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VInt (m - n))))),
              ("NEG", (TArrow TInt TInt,
                       VBuiltin (\(VInt m) -> VInt (-m)))),
              ("MUL", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VInt (m * n))))),
              ("QUOT", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VInt (m `quot` n))))),
              ("REM", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VInt (m `rem` n))))),
              ("DIV", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VInt (m `div` n))))),
              ("MOD", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VInt (m `mod` n))))),
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

-- | The collection of all built-in operations.
builtin_all :: Map String (Type, Value)
builtin_all = Map.union builtin_gates builtin_operations
