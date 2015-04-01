-- | This module contains the definition of the built-in operations that are made available to Proto-Quipper
-- code. This includes all the basic gates and some integer operations and comparisons.
module Builtins (
  defineBuiltins
  ) where

import Utils

import Interpreter.Circuits
import Interpreter.Values hiding (int, bool, unit)
import qualified Interpreter.Values as V (int, bool, unit)

import Monad.Error
import Monad.Core

import Core.Syntax
import Core.Environment as E

import qualified Compiler.SimplSyntax as C

import Data.Map as Map
import Data.IntMap as IntMap
import Data.List as List
import qualified Data.Char as Char



-- | Define the type @list@, with two constructors @_Cons@ and @_Nil@.
-- The return value includes the references of the type @list@, of the constructors @cons@ and @nil@.
--define_list :: Core (Algebraic, Datacon, Datacon)
--define_list = do
--  a <- fresh_type
--  n <- fresh_flag
--  m <- fresh_flag
--  p <- fresh_flag
--  q <- fresh_flag
--  list <- register_algebraic "list" Typedef {
--    arguments = [Covariant],
--    definition = ([], [])
--  }
--  let an = TypeAnnot n $ TypeVar a
--      acons = TypeAnnot p $ tensor [an, TypeAnnot q $ TAlgebraic list [an]]
--      tcons = TypeScheme [n,m,p,q] [a] ([],[Le m p noInfo]) (TypeAnnot one $ TArrow acons (TypeAnnot m $ TAlgebraic list [an]))
--      tnil = TypeScheme [n,m] [a] emptyset (TypeAnnot m $ TAlgebraic list [an])

--  cons <- register_datacon "_Cons" Datacondef {
--    datatype = list,
--    dtype = tcons,
--    tag = 1,
--    implementation = -1,
--    construct = Left C.EUnit,
--    deconstruct = \x -> C.EVar x
--  }
--  nil <- register_datacon "_Nil" Datacondef {
--    datatype = list,
--    dtype = tnil,
--    tag = 0,
--    implementation = -1,
--    construct = Left C.EUnit,
--    deconstruct = \x -> C.EVar x
--  }
--  update_algebraic list $ \alg -> Just alg { definition = ([an], [(cons, Just acons), (nil, Nothing)]) }
--  return (list, cons, nil)


-- | Define the type @char@ (as an algebraic type with one constructor @_Char@).
--define_char :: Core (Algebraic, Datacon)
--define_char = do
--  char <- register_algebraic "char" Typedef {
--    arguments = [],
--    definition = ([], [])
--  }
--  let tchar = TypeScheme [] [] emptyset (arrow int (TypeAnnot 1 $ TAlgebraic char []))

--  dchar <- register_datacon "_Char" Datacondef {
--    datatype = char,
--    dtype = tchar,
--    tag = 0,
--    implementation = -1,
--    construct = Left C.EUnit,
--    deconstruct = \x -> C.EVar x
--  }
--  update_algebraic char $ \alg -> Just alg { definition = ([], [(dchar, Just int)]) }
--  return (char, dchar)



-- | Extract an integer from a value, or throw a 'BuiltinError' otherwise. The second argument is
-- the name of the built-in operation that should appear in the error message.
getInt :: Value -> String -> Int
getInt (VConstant (ConstInt n)) _ = n
getInt _ s = throwNE $ BuiltinError s "an integer"

-- | Extract a boolean from a value, or throw a 'BuiltinError' otherwise. The second argument is
-- the name of the built-in operation that should appear in the error message.
getBool :: Value -> String -> Bool
getBool (VConstant (ConstBool b)) _ = b
getBool _ s = throwNE $ BuiltinError s "a boolean"

-- | Extract a tuple of size 2 from a value, or throw a 'BuiltinError'.
getPair :: Value -> String -> (Value, Value)
getPair (VTuple [a,b]) _ = (a,b)
getPair _ s = throwNE $ BuiltinError s "a tuple (_,_)"

-- | Extract a tuple of two integers from a value, or throw a 'BuiltinError'.
getIntPair :: Value -> String -> (Int, Int)
getIntPair (VTuple [a,b]) s = (getInt a s, getInt b s)
getIntPair _ s = throwNE $ BuiltinError s "a tuple (int,int)"

-- | Extract a string from a value, or throw a 'BuiltinError' otherwise. The second argument is the
-- name of the built-in operation that should appear in the error message.
getString :: Value -> String -> String
getString (VDatacon _ Nothing) _ = ""
getString (VDatacon _ (Just (VTuple [VDatacon _ (Just (VConstant (ConstInt c))), rest]))) s =
  (Char.chr c):(getString rest s)
getString v s =  throwNE $ BuiltinError s "a string"



-- | The type of all unary gates, i.e., @circ (qubit, qubit)@.
unaryType :: Type
unaryType = circ qubit qubit

-- | The type of all binary gates, i.e., @circ (qubit * qubit, qubit * qubit)@.
binaryType :: Type
binaryType = circ (tensor0 [qubit, qubit]) (tensor0 [qubit, qubit])


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
unaryGate :: String -> Value
unaryGate g =
  VCirc (VQubit 0) (Circ {
    qIn = [0],
    gates = [ Unary g 0 ],
    qOut = [0],
    qubit_id = 1,
    unused_ids = []
  }) (VQubit 0)


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
binaryGate :: String -> Value
binaryGate g =
  VCirc (VTuple [VQubit 0, VQubit 1])
        (Circ { qIn = [0, 1],
          gates = [ Binary g 0 1 ],
          qOut = [0, 1],
          qubit_id = 2,
          unused_ids = [] })
        (VTuple [VQubit 0, VQubit 1])


-- | Subset of the built-in values that provides the definitions of the gates. Below is the exact
-- list of all the defined gates, given by their reference label.
--
-- * The unary gates are : INIT0, INIT1, TERM0, TERM1, PHASE, GATE_H, NOT, GATE_X, GATE_Y, GATE_Z,
--   GATE_S, GATE_S_INV, GATE_T, GATE_T_INV, GATE_E, GATE_E_INV, GATE_OMEGA, GATE_V, GATE_V_INV.
--
-- * The binary gates are : CNOT, SWAP, CONTROL_PHASE, GATE_W.
--
-- * One ternary gate is defined: TOFFOLI.
--
-- Note that the list of unary and binary gates is actually provided by the "Interpreter.Circuits"
-- module.

-- | Subset of the built-in values that provides the definition of the built-in integer operations.
-- The list of currently defined operations is: +, -, *, QUOT, REM, DIV, MOD, POW, <=, >=, <, >, ==,
-- NE. It is bound to be extended, for example with more comparisons.

-- | Build the interfaces of the Builtins (and Core) modules.
defineBuiltins :: Core ()
defineBuiltins = do
  -- Definition of builtin types.
  --(list, cons, nil) <- define_list
  --(char, dchar) <- define_char

  -- Definition of basic operations.
  let intPairToInt = arrow (tensor [int, int]) int
      intPairToBool = arrow (tensor [int, int]) bool
  let ops = [
        ("add", intPairToInt, VBuiltin (\arg -> let (m, n) = getIntPair arg "add" in V.int (m + n))),
        ("sub", intPairToInt, VBuiltin (\arg -> let (m, n) = getIntPair arg "sub" in V.int (m - n))),
        ("mul", intPairToInt, VBuiltin (\arg -> let (m, n) = getIntPair arg "mul" in V.int (m * n))),
        ("quot", intPairToInt, VBuiltin (\arg -> let (m, n) = getIntPair arg "quot" in V.int (m `quot` n))),
        ("div", intPairToInt, VBuiltin (\arg -> let (m, n) = getIntPair arg "div" in V.int (m `div` n))),
        ("rem", intPairToInt, VBuiltin (\arg -> let (m, n) = getIntPair arg "rem" in V.int (m `rem` n))),
        ("mod", intPairToInt, VBuiltin (\arg -> let (m, n) = getIntPair arg "mod" in V.int (m `mod` n))),
        ("pow", intPairToInt, VBuiltin (\arg -> let (m, n) = getIntPair arg "pow" in V.int (m ^ n))),
        ("le", intPairToBool, VBuiltin (\arg -> let (m, n) = getIntPair arg "le" in V.bool (m <= n))),
        ("ge", intPairToBool, VBuiltin (\arg -> let (m, n) = getIntPair arg "ge" in V.bool (m >= n))),
        ("lt", intPairToBool, VBuiltin (\arg -> let (m, n) = getIntPair arg "lt" in V.bool (m < n))),
        ("gt", intPairToBool, VBuiltin (\arg -> let (m, n) = getIntPair arg "gt" in V.bool (m > n))),
        ("eq", intPairToBool, VBuiltin (\arg -> let (m, n) = getIntPair arg "eq" in V.bool (m == n))),
        ("neq", intPairToBool, VBuiltin (\arg -> let (m, n) = getIntPair arg "neq" in V.bool (m /= n))),
        ("neg", arrow int int, VBuiltin (\n -> V.int (- getInt n "neg")))
        ]

  -- Some printing functions.
  let print = [
        ("print_int", arrow int unit, VBuiltin (\arg -> V.unit)),
        ("print_newline", arrow unit unit, VBuiltin (\arg -> arg))
        ]

  -- Definition of some basic gates.
  let init = [
        ("g_init0", circ unit qubit, VCirc V.unit (singleton_circuit $ Init 0 0) (VQubit 0)),
        ("g_init1", circ unit qubit, VCirc V.unit (singleton_circuit $ Init 1 0) (VQubit 0))
        ]

  let term = [
        ("g_term0", circ qubit unit, VCirc (VQubit 0) (singleton_circuit $ Term 0 0) V.unit),
        ("g_term1", circ qubit unit, VCirc (VQubit 0) (singleton_circuit $ Term 1 0) V.unit)
        ]

  let phase = [
        ("g_phase", arrow int unaryType, VBuiltin (\n -> VCirc (VQubit 0) (singleton_circuit $ Phase (getInt n "G_PHASE") 0) (VQubit 0))),
        ("g_control_phase", arrow (tensor [int,bool]) binaryType,
                            VBuiltin (\param ->
                              let (n, sign) = getPair param "G_CONTROL_PHASE" in
                              VCirc (VTuple [VQubit 0, VQubit 1])
                                    (singleton_circuit $ Controlled (Phase (getInt n "G_CONTROL_PHASE") 0) [(1, getBool sign "G_CONTROL_PHASE")])
                                    (VTuple [VQubit 0, VQubit 1])))
        ]

  let ceitz = [
        ("g_control_eitz", arrow bool binaryType,
                               VBuiltin (\sign ->
                                 VCirc (VTuple [VQubit 0, VQubit 1])
                                       (singleton_circuit $ Controlled (Unary "G_EITZ" 0) [(1, getBool sign "G_CONTROL_EITZ")])
                                       (VTuple [VQubit 0, VQubit 1])))
        ]

  let unary = List.map (\(g, _) -> (toLower g, unaryType, unaryGate g)) unary_gates
  let binary = List.map (\(g, _) -> (toLower g, binaryType, binaryGate g)) binary_gates

  let others = [
        ("g_cnot", arrow bool $ circ (tensor0 [qubit, qubit]) (tensor0 [qubit, qubit]),
                    VBuiltin (\sign ->
                      VCirc (VTuple [VQubit 0, VQubit 1])
                            (singleton_circuit $ Controlled (Unary "G_NOT" 0) [(1, getBool sign "G_CNOT")])
                             (VTuple [VQubit 0, VQubit 1]))),
        ("g_toffoli", arrow (tensor [bool, bool]) $ circ (tensor0 [qubit, qubit, qubit]) (tensor0 [qubit, qubit, qubit]),
                     VBuiltin (\param ->
                       let (sign1, sign2) = getPair param "G_TOFFOLI" in
                       VCirc (VTuple [VQubit 0, VQubit 1, VQubit 2])
                             (singleton_circuit $ Controlled (Unary "G_NOT" 0) [(1, getBool sign1 "G_TOFFOLI"),(2, getBool sign2 "G_TOFFOLI")])
                             (VTuple [VQubit 0, VQubit 1, VQubit 2])))
        ]


  -- Compilation specifics. Note that the variables are all given a dummy type and value.
  let compile = [
        ("UNENCAP", arrow int int, V.unit),
        ("OPENBOX", arrow int int, V.unit),
        ("CLOSEBOX", arrow int int, V.unit),
        ("REV", arrow int int, V.unit),
        ("APPBIND", arrow int int, V.unit),
        ("ISREF", arrow int int, V.unit),
        ("ERROR", arrow int int, V.unit)
        ]

  let builtins = Module {
      moduleName = "Builtins",
      filePath = "",
      environment = Environment {
          variables = Map.empty,
          types = Map.empty,
          constructors = Map.empty
        },
      typemap = IntMap.empty,
      valuation = IntMap.empty
    }
  -- Import the preceding definitions.
  builtins <- List.foldl (\rec (name, typ, val) -> do
        builtins <- rec
        x <- registerVariable (Just "Builtins") name
        return builtins {
            typemap = IntMap.insert x (schemeOfType typ) $ typemap builtins,
            valuation = IntMap.insert x val $ valuation builtins,
            environment = (environment builtins) {
                variables = Map.insert name (Global x) $ variables $ environment builtins
              }
          }
      ) (return builtins) $ ops ++ print ++ init ++ term ++ phase ++ ceitz ++ unary ++ binary ++ others ++ compile
  -- Insert the new module at the core.
  define builtins


  -- Define a generic printing function for circuits.
  --vprint <- register_var (Just "Builtins") "print_circ" 0
  --a <- fresh_type
  --n <- fresh_flag
  --b <- fresh_type
  --m <- fresh_flag
  --insert_global vprint (TypeScheme [n,m] [a,b] emptyset $ arrow (circ (TypeAnnot n $ TypeVar a) (TypeAnnot m $ TypeVar b)) unit) Nothing
  --lbl <- return $ Map.insert "print_circ" (Global vprint) lbl

  -- Build the module.
  --let builtins = Module {
  --  environment = Environment {
  --    variables = lbl,
  --    types = Map.fromList [("list", TypeAnnot 1 $ TAlgebraic list []), ("char", TypeAnnot 1 $ TAlgebraic char [])],
  --    E.datacons = Map.fromList [("_Cons", cons), ("_Nil", nil), ("_Char", dchar)]
  --  },
  --  declarations = []
  --}

  --ctx <- get_context
  --set_context ctx {
  --  modules = ("Builtins", builtins):(modules ctx)
  --}

  -- Compiler specifics.
  --choose_implementation list
  --choose_implementation char
