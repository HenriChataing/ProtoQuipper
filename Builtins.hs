-- | This module contains the definition of the built-in operations that are made available to Proto-Quipper
-- code. This includes all the basic gates and some integer operations and comparisons.
module Builtins (
  define_builtins
  ) where

import Utils

import Interpret.Circuits
import Interpret.Values

import Monad.QuipperError
import Monad.QpState hiding (qubit_id)
import Monad.Modules as M

import Core.Syntax
import Core.LabellingContext as L

import qualified Compiler.SimplSyntax as C

import Data.Map as Map
import Data.List as List
import qualified Data.Char as Char



-- | Define the type @list@, with two constructors @_Cons@ and @_Nil@.
-- The return value includes the references of the type @list@, of the constructors @cons@ and @nil@.
define_list :: QpState (Algebraic, Datacon, Datacon)
define_list = do
  a <- fresh_type
  n <- fresh_flag
  m <- fresh_flag
  p <- fresh_flag
  q <- fresh_flag
  list <- register_algebraic "list" Typedef {
    arguments = [Covariant],
    definition = ([], [])
  }
  let an = TBang n $ TVar a
      acons = TBang p $ TTensor [an, TBang q $ TAlgebraic list [an]]
      tcons = TForall [n,m,p,q] [a] ([],[Le m p no_info]) (TBang one $ TArrow acons (TBang m $ TAlgebraic list [an]))
      tnil = TForall [n,m] [a] emptyset (TBang m $ TAlgebraic list [an])

  cons <- register_datacon "_Cons" Datacondef {
    datatype = list,
    dtype = tcons,
    tag = 1,
    implementation = -1,
    construct = Left C.EUnit,
    deconstruct = \x -> C.EVar x
  }
  nil <- register_datacon "_Nil" Datacondef {
    datatype = list,
    dtype = tnil,
    tag = 0,
    implementation = -1,
    construct = Left C.EUnit,
    deconstruct = \x -> C.EVar x
  }
  update_algebraic list $ \alg -> Just alg { definition = ([an], [(cons, Just acons), (nil, Nothing)]) }
  return (list, cons, nil)


-- | Define the type @char@ (as an algebraic type with one constructor @_Char@).
define_char :: QpState (Algebraic, Datacon)
define_char = do
  char <- register_algebraic "char" Typedef {
    arguments = [],
    definition = ([], [])
  }
  let tchar = TForall [] [] emptyset (arrow int (TBang 1 $ TAlgebraic char []))

  dchar <- register_datacon "_Char" Datacondef {
    datatype = char,
    dtype = tchar,
    tag = 0,
    implementation = -1,
    construct = Left C.EUnit,
    deconstruct = \x -> C.EVar x
  }
  update_algebraic char $ \alg -> Just alg { definition = ([], [(dchar, Just int)]) }
  return (char, dchar)



-- | Extract an integer from a value, or throw a 'BuiltinError'
-- otherwise. The second argument is the name of the built-in
-- operation that should appear in the error message.
unVInt :: Value -> String -> Int
unVInt (VInt n) _ = n
unVInt _ s = throwNE (BuiltinError s "an integer")


-- | Extract a boolean from a value, or throw a 'BuiltinError'
-- otherwise. The second argument is the name of the built-in
-- operation that should appear in the error message.
unVBool :: Value -> String -> Bool
unVBool (VBool b) _ = b
unVBool _ s = throwNE (BuiltinError s "a boolean")


-- | Extract a string from a value, or throw a 'BuiltinError'
-- otherwise. The second argument is the name of the built-in
-- operation that should appear in the error message.
unVString :: Value -> String -> String
unVString (VDatacon _ Nothing) _ = ""
unVString (VDatacon _ (Just (VTuple [VDatacon _ (Just (VInt c)), rest]))) s =
  (Char.chr c):(unVString rest s)
unVString v s =  throwNE (BuiltinError s "a string")



-- | The type of all unary gates, i.e., @circ (qubit, qubit)@.
unary_type :: Type
unary_type = circ qubit qubit


-- | The type of all binary gates, i.e., @circ (qubit * qubit, qubit * qubit)@.
binary_type :: Type
binary_type = circ (TBang zero $ TTensor [qubit, qubit]) (TBang zero $ TTensor [qubit, qubit])


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





-- | Subset of the built-in values that provides the definition of the built-in integer operations.
-- The list of currently defined operations is: +, -, *, QUOT, REM, DIV, MOD, POW, <=, >=, <, >, ==, NE. It is bound to be extended, for
-- example with more comparisons.



-- | Build the interface of the Builtins module.
define_builtins :: QpState ()
define_builtins = do
  -- Definition of builtin types.
  (list, cons, nil) <- define_list
  (char, dchar) <- define_char

  -- Definition of basic operations.
  let ops = [
        ("+", (arrow int $ arrow int int, VBuiltin (\m -> VBuiltin (\n -> VInt (unVInt m "+" + unVInt n "+"))))),
        ("-", (arrow int $ arrow int int, VBuiltin (\m -> VBuiltin (\n -> VInt (unVInt m "-" - unVInt n "-"))))),
        ("neg", (arrow int int, VBuiltin (\m -> VInt (-unVInt m "NEG")))),
        ("*", (arrow int $ arrow int int, VBuiltin (\m -> VBuiltin (\n -> VInt (unVInt m "*" * unVInt n "*"))))),
        ("/", (arrow int $ arrow int int, VBuiltin (\m -> VBuiltin (\n -> VInt (unVInt m "quot" `quot` unVInt n "quot"))))),
        ("div", (arrow int $ arrow int int, VBuiltin (\m -> VBuiltin (\n -> VInt (unVInt m "div" `div` unVInt n "div"))))),
        ("%", (arrow int $ arrow int int, VBuiltin (\m -> VBuiltin (\n -> VInt (unVInt m "rem" `rem` unVInt n "rem"))))),
        ("mod", (arrow int $ arrow int int, VBuiltin (\m -> VBuiltin (\n -> VInt (unVInt m "mod" `mod` unVInt n "mod"))))),
        ("^", (arrow int $ arrow int int, VBuiltin (\m -> VBuiltin (\n -> VInt (unVInt m "^" ^ unVInt n "^"))))),
        ("<=", (arrow int $ arrow int bool, VBuiltin (\m -> VBuiltin (\n -> VBool (unVInt m "<=" <= unVInt n "<="))))),
        (">=", (arrow int $ arrow int bool, VBuiltin (\m -> VBuiltin (\n -> VBool (unVInt m ">=" >= unVInt n ">="))))),
        ("<", (arrow int $ arrow int bool, VBuiltin (\m -> VBuiltin (\n -> VBool (unVInt m "<" < unVInt n "<"))))),
        (">", (arrow int $ arrow int bool, VBuiltin (\m -> VBuiltin (\n -> VBool (unVInt m ">" > unVInt n ">"))))),
        ("==", (arrow int $ arrow int bool, VBuiltin (\m -> VBuiltin (\n -> VBool (unVInt m "==" == unVInt n "=="))))),
        ("<>", (arrow int $ arrow int bool, VBuiltin (\m -> VBuiltin (\n -> VBool (unVInt m "/=" /= unVInt n "/=")))))
        ]

  -- Definition of some basic gates.
  let init = [
        ("g_init0", (circ unit qubit, VCirc VUnit (singleton_circuit $ Init 0 0) (VQubit 0))),
        ("g_init1", (circ unit qubit, VCirc VUnit (singleton_circuit $ Init 1 0) (VQubit 0)))
        ]

  let term = [
        ("g_term0", (circ qubit unit, VCirc (VQubit 0) (singleton_circuit $ Term 0 0) VUnit)),
        ("g_term1", (circ qubit unit, VCirc (VQubit 0) (singleton_circuit $ Term 1 0) VUnit))
        ]

  let phase = [
        ("g_phase", (arrow int unary_type,
                   VBuiltin (\n -> VCirc (VQubit 0) (singleton_circuit $ Phase (unVInt n "G_PHASE") 0) (VQubit 0)))),
        ("g_control_phase", (arrow int $ arrow bool binary_type,
                           VBuiltin (\n ->
                           VBuiltin (\sign ->
                              VCirc (VTuple [VQubit 0, VQubit 1])
                                    (singleton_circuit $ Controlled (Phase (unVInt n "G_CONTROL_PHASE") 0) [(1, unVBool sign "G_CONTROL_PHASE")])
                                    (VTuple [VQubit 0, VQubit 1])))))
        ]

  let ceitz = [
        ("g_control_eitz", (arrow bool binary_type,
                               VBuiltin (\sign ->
                                 VCirc (VTuple [VQubit 0, VQubit 1])
                                       (singleton_circuit $ Controlled (Unary "G_EITZ" 0) [(1, unVBool sign "G_CONTROL_EITZ")])
                                       (VTuple [VQubit 0, VQubit 1]))))
        ]

  let unary = List.map (\(g, _) -> (toLower g, (unary_type, unary_value g))) unary_gates
  let binary = List.map (\(g, _) -> (toLower g, (binary_type, binary_value g))) binary_gates

  let others = [
        ("g_cnot", (TBang 1 $ TArrow bool $ circ (TBang 0 $ TTensor [qubit, qubit]) (TBang 0 $ TTensor [qubit, qubit]),
                    VBuiltin (\sign ->
                      VCirc (VTuple [VQubit 0, VQubit 1])
                            (singleton_circuit $ Controlled (Unary "G_NOT" 0) [(1, unVBool sign "G_CNOT")])
                             (VTuple [VQubit 0, VQubit 1])))),
        ("g_toffoli", (TBang 1 $ TArrow bool $ TBang 1 $ TArrow bool $ circ (TBang 0 $ TTensor [qubit, qubit, qubit]) (TBang 0 $ TTensor [qubit, qubit, qubit]),
                     VBuiltin (\sign1 ->
                     VBuiltin (\sign2 ->
                       VCirc (VTuple [VQubit 0, VQubit 1, VQubit 2])
                             (singleton_circuit $ Controlled (Unary "G_NOT" 0) [(1, unVBool sign1 "G_TOFFOLI"),(2, unVBool sign2 "G_TOFFOLI")])
                             (VTuple [VQubit 0, VQubit 1, VQubit 2]))))) ]

  -- Error builtin.
  a <- fresh_type
  n <- fresh_flag
  let error = [ ("error", (TForall [n] [a] emptyset $ arrow (TBang 1 $ TAlgebraic list [TBang 1 $ TAlgebraic char []]) (TBang n $ TVar a),
                           VBuiltin (\msg -> let string_msg = unVString msg "ERROR" in throwNE (UserError string_msg)))) ]


  -- Import the preceding definitions.
  lbl <- List.foldl (\rec (b, (typ, val)) -> do
        lbl <- rec
        vb <- register_var (Just "Builtins") b 0
        insert_global vb (typescheme_of_type typ) (Just val)
        return $ Map.insert b (LGlobal vb) lbl
      ) (return Map.empty) $ ops ++ init ++ term ++ phase ++ ceitz ++ unary ++ binary ++ others

  -- Compilation stuff (with no type nor value).
  lbl' <- List.foldl (\rec b -> do
        lbl <- rec
        vb <- register_var (Just "Builtins") b 0
        return $ Map.insert b (LGlobal vb) lbl
      ) (return Map.empty) ["UNENCAP", "OPENBOX", "CLOSEBOX", "REV", "APPBIND", "ISREF", "PATTERN_ERROR"]

  -- Build the module.
  let builtins = Mod {
    labelling = LblCtx {
      variables = Map.union lbl lbl',
      types = Map.fromList [("list", TBang 1 $ TAlgebraic list []), ("char", TBang 1 $ TAlgebraic char [])],
      L.datacons = Map.fromList [("_Cons", cons), ("_Nil", nil), ("_Char", dchar)] },
    declarations = []
  }

  ctx <- get_context
  set_context ctx {
    modules = ("Builtins", builtins):(modules ctx)
  }


