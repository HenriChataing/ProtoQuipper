-- | This module contains the definition of the built-in operations that are made available to Proto-Quipper
-- code. This includes all the basic gates and some integer operations and comparisons.
module Builtins where

import Parsing.Syntax

import Interpret.Circuits
import Interpret.Values

import Monad.QuipperError

import Control.Exception
import Data.Map as Map
import Data.List as List


-- | Extract an integer from a value, or throw a 'BuiltinError'
-- otherwise. The second argument is the name of the built-in
-- operation that should appear in the error message.
unVInt :: Value -> String -> Int
unVInt (VInt n) _ = n
unVInt _ s = throw $ BuiltinError s "an integer"


-- | Extract a boolean from a value, or throw a 'BuiltinError'
-- otherwise. The second argument is the name of the built-in
-- operation that should appear in the error message.
unVBool :: Value -> String -> Bool
unVBool (VBool b) _ = b
unVBool _ s = throw $ BuiltinError s "a boolean"


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
                          VBuiltin (\n -> VCirc (VQubit 0) (singleton_circuit $ Phase (unVInt n "PHASE") 0) (VQubit 0)))),
               ("CONTROL_PHASE", (TArrow TInt (TArrow TBool binary_type),
                                  VBuiltin (\n -> 
                                             VBuiltin (\sign -> 
                                                        VCirc (VTuple [VQubit 0, VQubit 1])
                                                              (singleton_circuit $ Controlled (Phase (unVInt n "CONTROL_PHASE") 0) [(1, unVBool sign "CONTROL_PHASE")]) 
                                                              (VTuple [VQubit 0, VQubit 1]))))) ] in

  let ceitz = [("CONTROL_GATE_EITZ", (TArrow TBool binary_type,
                                  VBuiltin (\sign ->
                                             VCirc (VTuple [VQubit 0, VQubit 1])
                                                   (singleton_circuit $ Controlled (Unary "GATE_EITZ" 0) [(1, unVBool sign "CONTROL_GATE_EITZ")])
                                                   (VTuple [VQubit 0, VQubit 1])))) ] in

  let unary = List.map (\(g, _) -> (g, (unary_type, unary_value g))) unary_gates in
  let binary = List.map (\(g, _) -> (g, (binary_type, binary_value g))) binary_gates in

  let cnot = [("CNOT", (TArrow TBool (TCirc (TTensor [TQubit, TQubit]) (TTensor [TQubit, TQubit])),
                             VBuiltin (\sign ->
                                        VCirc (VTuple [VQubit 0, VQubit 1])
                                              (singleton_circuit $ Controlled (Unary "NOT" 0) [(1, unVBool sign "CNOT")])
                                              (VTuple [VQubit 0, VQubit 1])))),
              ("TOFFOLI", (TArrow TBool (TArrow TBool (TCirc (TTensor [TQubit, TQubit, TQubit]) (TTensor [TQubit, TQubit, TQubit]))),
                             VBuiltin (\sign1 ->
                                        VBuiltin (\sign2 ->
                                                   VCirc (VTuple [VQubit 0, VQubit 1, VQubit 2])
                                                         (singleton_circuit $ Controlled (Unary "NOT" 0) [(1, unVBool sign1 "TOFFOLI"),(2, unVBool sign2 "TOFFOLI")])
                                                         (VTuple [VQubit 0, VQubit 1, VQubit 2]))))) ] in

  Map.fromList (cnot ++ init ++ term ++ unary ++ phase ++ ceitz ++ binary)





-- | Subset of the built-in values that provides the definition of the built-in integer operations.
-- The list of currently defined operations is: ADD, SUB, MUL, QUOT, REM, DIV, MOD, POW, LE, GE, LT, GT, EQ, NE. It is bound to be extended, for
-- example with more comparisons.
builtin_operations :: Map String (Type, Value)
builtin_operations =
  let ops = [ ("ADD", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\m -> VBuiltin (\n -> VInt (unVInt m "ADD" + unVInt n "ADD"))))),
              ("SUB", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\m -> VBuiltin (\n -> VInt (unVInt m "SUB" - unVInt n "SUB"))))),
              ("NEG", (TArrow TInt TInt,
                       VBuiltin (\m -> VInt (-unVInt m "NEG")))),
              ("MUL", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\m -> VBuiltin (\n -> VInt (unVInt m "MUL" * unVInt n "MUL"))))),
              ("QUOT", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\m -> VBuiltin (\n -> VInt (unVInt m "QUOT" `quot` unVInt n "QUOT"))))),
              ("REM", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\m -> VBuiltin (\n -> VInt (unVInt m "REM" `rem` unVInt n "REM"))))),
              ("DIV", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\m -> VBuiltin (\n -> VInt (unVInt m "DIV" `div` unVInt n "DIV"))))),
              ("MOD", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\m -> VBuiltin (\n -> VInt (unVInt m "MOD" `mod` unVInt n "MOD"))))),
              ("POW", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\m -> VBuiltin (\n -> VInt (unVInt m "POW" ^ unVInt n "POW"))))),
              ("LE", (TArrow TInt (TArrow TInt TBool),
                      VBuiltin (\m -> VBuiltin (\n -> VBool (unVInt m "LE" <= unVInt n "LE"))))),
              ("GE", (TArrow TInt (TArrow TInt TBool),
                      VBuiltin (\m -> VBuiltin (\n -> VBool (unVInt m "GE" >= unVInt n "GE"))))),
              ("LT", (TArrow TInt (TArrow TInt TBool),
                      VBuiltin (\m -> VBuiltin (\n -> VBool (unVInt m "LT" < unVInt n "LT"))))),
              ("GT", (TArrow TInt (TArrow TInt TBool),
                      VBuiltin (\m -> VBuiltin (\n -> VBool (unVInt m "GT" > unVInt n "GT"))))),
              ("EQ", (TArrow TInt (TArrow TInt TBool),
                      VBuiltin (\m -> VBuiltin (\n -> VBool (unVInt m "EQ" == unVInt n "EQ"))))), 
              ("NE", (TArrow TInt (TArrow TInt TBool),
                      VBuiltin (\m -> VBuiltin (\n -> VBool (unVInt m "NE" /= unVInt n "NE")))))
            ] in
  Map.fromList ops


-- | Built-in user error mechanism.
builtin_error :: Map String (Type, Value)
builtin_error =
  Map.singleton "ERROR" (TForall "_a_" $ TArrow (TApp (TVar "list") (TVar "char")) (TVar "_a_"),
                         VBuiltin (\msg -> 
                                     let string_msg = string_of_value msg in 
                                     throw $ UserError string_msg))


-- | The collection of all built-in operations.
builtin_all :: Map String (Type, Value)
builtin_all = Map.union builtin_gates $ Map.union builtin_operations builtin_error



