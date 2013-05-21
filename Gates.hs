module Gates where

import Syntax

import Data.Map as Map
import Data.List as List

----------------------------------------------
-------------- Unary gates -------------------

-- Name of the gates
unaryGates :: [String]
----------------------
unaryGates =
  [ "H", "NOT", "Y", "Z", "S", "T", "IS", "IT" ]

-- Attribution of the inverses
unaryRev :: [(String, String)]
------------------------------
unaryRev =
  [ ("H", "H"),
    ("NOT", "NOT"), ("Y", "Y"), ("Z", "Z"),
    ("S", "IS"), ("IS", "S"),
    ("T", "IT"), ("IT", "T") ]

-- Symbolic representation
unarySym :: [(String, String)]
------------------------------
unarySym =
  [ ("H", "[H]"),
    ("NOT", "(X)"),
    ("Y", "[Y]"), ("Z", "[Z]"),
    ("S", "[S]"), ("IS", "[\x0305S]"),
    ("T", "[T]"), ("IT", "[\x0305T]") ]

-- General type for unary gates
unaryType :: Type
-----------------
unaryType = TCirc TQBit TQBit

----------------------------------------------
------------- Binary gates -------------------

-- Name if the gates
binaryGates :: [String]
-----------------------
binaryGates =
  [ "SWAP", "CNOT" ]

-- Attribution of the inverses
binaryRev :: [(String, String)]
-------------------------------
binaryRev =
  [ ("SWAP", "SWAP"),
    ("CNOT", "CNOT") ]

-- Symbolic representation
binarySym :: [(String, (String, String))]
---------------------------------------
binarySym =
  [ ("SWAP", ("-X-", "-X-")),
    ("CNOT", ("(+)", "-*-")) ]

-- General type for binary gates
binaryType :: Type
------------------
binaryType = TCirc (TTensor TQBit TQBit) (TTensor TQBit TQBit)

----------------------------------------------
------------- Typing environment -------------

-- Generation of the typing environment
typingEnvironment :: [(String, Type)]
------------------------------------
typingEnvironment =
  let initTypes = [("INIT0", TCirc TUnit TQBit), ("INIT1", TCirc TUnit TQBit)] in
  let termTypes = [("TERM0", TCirc TQBit TUnit), ("TERM1", TCirc TQBit TUnit)] in
  let unaryTypes = List.map (\s -> (s, unaryType)) unaryGates in
  let binaryTypes = List.map (\s -> (s, binaryType)) binaryGates in

  initTypes ++ termTypes ++ unaryTypes ++ binaryTypes

