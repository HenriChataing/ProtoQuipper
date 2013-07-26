module Gates where

import Syntax

import Data.Map as Map
import Data.List as List

----------------------------------------------
-------------- Unary gates -------------------

-- Name of the gates
unary_gates :: [String]
----------------------
unary_gates =
  [ "H", "NOT", "Y", "Z", "S", "T", "IS", "IT" ]

-- Attribution of the inverses
unary_rev :: [(String, String)]
------------------------------
unary_rev =
  [ ("H", "H"),
    ("NOT", "NOT"), ("Y", "Y"), ("Z", "Z"),
    ("S", "IS"), ("IS", "S"),
    ("T", "IT"), ("IT", "T") ]

-- Symbolic representation
unary_sym :: [(String, String)]
------------------------------
unary_sym =
  [ ("H", "[H]"),
    ("NOT", "(X)"),
    ("Y", "[Y]"), ("Z", "[Z]"),
    ("S", "[S]"), ("IS", "[\x0305S]"),
    ("T", "[T]"), ("IT", "[\x0305T]") ]

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
  [ "SWAP", "CNOT" ]

-- Attribution of the inverses
binary_rev :: [(String, String)]
-------------------------------
binary_rev =
  [ ("SWAP", "SWAP"),
    ("CNOT", "CNOT") ]

-- Symbolic representation
binary_sym :: [(String, (String, String))]
---------------------------------------
binary_sym =
  [ ("SWAP", ("-X-", "-X-")),
    ("CNOT", ("(+)", "-*-")) ]

-- General type for binary gates
binary_type :: Type
------------------
binary_type = TCirc (TTensor [TQBit, TQBit]) (TTensor [TQBit, TQBit])

