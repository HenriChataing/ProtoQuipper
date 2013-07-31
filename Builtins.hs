module Builtins where

import Parsing.Syntax

import Interpret.Circuits
import Interpret.Values

import Data.Map as Map
import Data.List as List


-- | Type of all the unary gates.
unary_type :: Type
unary_type = TCirc TQBit TQBit


-- | Type of all the binary gates.
binary_type :: Type
binary_type = TCirc (TTensor [TQBit, TQBit]) (TTensor [TQBit, TQBit])


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


-- | Map of the builtin gates.
builtin_gates :: Map String (Type, Value)
builtin_gates =
  let init = [("INIT0", (TCirc TUnit TQBit,
                         VCirc VUnit (Circ { qIn = [], gates = [ Init 0 0 ], qOut = [0] }) (VQbit 0))),
              ("INIT1", (TCirc TUnit TQBit,
                         VCirc VUnit (Circ { qIn = [], gates = [ Init 0 1 ], qOut = [0] }) (VQbit 0)))] in

  let term = [("TERM0", (TCirc TQBit TUnit,
                         VCirc (VQbit 0) (Circ { qIn = [], gates = [ Term 0 0 ], qOut = [0] }) VUnit)),
              ("TERM1", (TCirc TQBit TUnit,
                         VCirc (VQbit 0) (Circ { qIn = [], gates = [ Term 0 1 ], qOut = [0] }) VUnit))] in

  let unary = List.map (\(g, _) -> (g, (unary_type, unary_value g))) unary_gates in
  let binary = List.map (\(g, _) -> (g, (binary_type, binary_value g))) binary_gates in

  let toffoli = ("TOFFOLI", (TCirc (TTensor [TQBit, TQBit, TQBit]) (TTensor [TQBit, TQBit, TQBit]),
                             VCirc (VTuple [VQbit 0, VQbit 1, VQbit 2])
                                   (Circ { qIn = [0, 1, 2], gates = [ Controlled (Unary "NOT" 0) [1, 2] ], qOut = [0, 1, 2] })
                                   (VTuple [VQbit 0, VQbit 1, VQbit 2]))) in

  Map.fromList (toffoli:(init ++ term ++ unary ++ binary))





-- | Generation of the builtin context : integer operations
builtin_operations :: Map String (Type, Value)
builtin_operations =
  let ops = [ ("ADD", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VInt (m + n))))),
              ("B", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VInt (m - n))))),
              ("MUL", (TArrow TInt (TArrow TInt TInt),
                       VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VInt (m * n))))),
              ("LT", (TArrow TInt (TArrow TInt TBool),
                      VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VBool (m < n))))),
              ("GT", (TArrow TInt (TArrow TInt TBool),
                      VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VBool (m > n))))),
              ("EQ", (TArrow TInt (TArrow TInt TBool),
                      VBuiltin (\(VInt m) -> VBuiltin (\(VInt n) -> VBool (m == n))))) ] in
  Map.fromList ops

