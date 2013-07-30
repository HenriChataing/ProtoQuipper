module Gates where

import Parsing.Syntax

import Data.Map as Map
import Data.List as List

----------------------------------------------
-------------- Unary gates -------------------

-- Name of the gates
unary_gates :: [String]
----------------------
unary_gates =
  [ "GATE_H", "NOT",
    "GATE_X", "GATE_Y", "GATE_Z",
    "GATE_S", "GATE_S_INV",
    "GATE_T", "GATE_T_INV",
    "GATE_E", "GATE_E_INV",
    "GATE_OMEGA",
    "GATE_V", "GATE_V_INV" ]

-- Attribution of the inverses
unary_rev :: [(String, String)]
------------------------------
unary_rev =
  [ ("GATE_H", "GATE_H"),
    ("NOT", "NOT"),
    ("GATE_X", "GATE_X"),
    ("GATE_Y", "GATE_Y"),
    ("GATE_Z", "GATE_Z"),
    ("GATE_S", "GATE_S_INV"),
    ("GATE_S_INV", "GATE_S"),
    ("GATE_T", "GATE_T_INV"),
    ("GATE_T_INV", "GATE_T"),
    ("GATE_E", "GATE_E_INV"),
    ("GATE_E_INV", "GATE_E"),
    ("GATE_OMEGA", "GATE_OMEGA"),
    ("GATE_V", "GATE_V_INV"),
    ("GATE_V_INV", "GATE_V") ]

-- Symbolic representation
unary_sym :: [(String, String)]
------------------------------
unary_sym =
  [ ("GATE_H", "[H]"),
    ("NOT", "(+)"),
    ("GATE_X", "(+)"),
    ("GATE_Y", "[Y]"),
    ("GATE_Z", "[Z]"),
    ("GATE_S", "[S]"),
    ("GATE_S_INV", "[\x0305S]"),
    ("GATE_T", "[T]"),
    ("GATE_T_INV", "[\x0305T]"),
    ("GATE_E", "[E]"),
    ("GATE_E_INV", "[\x0305\&E]"),
    ("GATE_OMEGA", "[\x03C9]"),
    ("GATE_V", "[V]"),
    ("GATE_V_INV", "[\x0305V]") ]

-- General type for unary gates
unary_type :: Type
-----------------
unary_type = TCirc TQBit TQBit

----------------------------------------------
------------- Binary gates -------------------

-- Name if the gates
binary_gates :: [String]
-----------------------
binary_gates =
  [ "SWAP", "CNOT", "GATE_W" ]

-- Attribution of the inverses
binary_rev :: [(String, String)]
-------------------------------
binary_rev =
  [ ("SWAP", "SWAP"),
    ("CNOT", "CNOT"),
    ("GATE_W", "GATE_W") ]

-- Symbolic representation
binary_sym :: [(String, (String, String))]
---------------------------------------
binary_sym =
  [ ("SWAP", ("-X-", "-X-")),
    ("CNOT", ("(+)", "-*-")),
    ("GATE_W", ("-W-", "-W-")) ]

-- General type for binary gates
binary_type :: Type
------------------
binary_type = TCirc (TTensor [TQBit, TQBit]) (TTensor [TQBit, TQBit])

