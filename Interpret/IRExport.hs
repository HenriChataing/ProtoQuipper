-- | Module that defines an IR export tool for circuits. The main function, export_to_IR, inputs a circuit (defined in module Circuit)
-- and outputs a string that contains the IR specification of the circuit.
module Interpret.IRExport where

import Interpret.Circuits

import qualified Data.List as List


-- | The type of the IR document file.
type IRDoc = String


-- | Creates a new IR document, and initialized with the input wires.
new_with_inputs :: [Int] -> IRDoc
new_with_inputs [] =
  "Inputs: none\n"

new_with_inputs inWires =
  let irdoc = List.foldl (\irdoc w -> irdoc ++ " " ++ show w ++ ":Qbit") "Inputs:" inWires in
  irdoc ++ "\n"
 

-- | Appends a single gate to the specification.
append_gate :: Gate -> IRDoc -> IRDoc
-- Init and term
append_gate (Init b w) irdoc = irdoc ++ "QInit" ++ show b ++ "(" ++ show w ++ ")\n"
append_gate (Term b w) irdoc = irdoc ++ "QTerm" ++ show b ++ "(" ++ show w ++ ")\n"

-- Unary gates
-- Some gates have a specific format in IR
append_gate (Phase n w) irdoc =
  let t = pi / ((fromIntegral n) :: Float) in
  irdoc ++ "QPhase(" ++ show w ++ ") with t=" ++ show t ++ "\n" 
-- And some don't
append_gate (Unary g w) irdoc =
  let (prg, inv) = case g of
                     "NOT" -> ("not", "")
                     "GATE_H" -> ("H", "")
                     "GATE_X" -> ("X", "")
                     "GATE_Y" -> ("Y", "")
                     "GATE_Z" -> ("Z", "")
                     "GATE_S" -> ("S", "")
                     "GATE_S_INV" -> ("S", "*")
                     "GATE_T" -> ("T", "")
                     "GATE_T_INV" -> ("T", "*")
                     "GATE_E" -> ("E", "")
                     "GATE_E_INV" -> ("E", "*")
                     "GATE_V" -> ("V", "")
                     "GATE_V_INV" -> ("V", "*")
    in
  irdoc ++ "QGate[\"" ++ prg ++ "\"]" ++ inv ++ "(" ++ show w ++ ")\n" 

-- Binary gates
append_gate (Binary "CNOT" w0 w1) irdoc =
  irdoc ++ "QGate[\"not\"](" ++ show w0 ++ ") with controls=[+" ++ show w1 ++ "]\n"
append_gate (Binary "SWAP" w0 w1) irdoc =
  irdoc ++ "QGate[\"swap\"](" ++ show w0 ++ " " ++ show w1 ++ ")\n"
append_gate (Binary "GATE_W" w0 w1) irdoc =
  irdoc ++ "QGate[\"W\"](" ++ show w0 ++ show w1 ++ ")\n"

-- Controlled gates
append_gate (Controlled g (c:rest)) irdoc =
  let prg = append_gate g "" in
  irdoc ++ List.init prg ++ " with controls=[+" ++ show c ++ List.foldl (\s w -> s ++ " +" ++ show w) "" rest ++"]\n"


-- | Prints the outputs of the circuit.
append_outputs :: [Int] -> IRDoc -> IRDoc
append_outputs [] irdoc =
  irdoc ++ "Outputs: none\n"

append_outputs outWires irdoc =
  irdoc ++ List.foldl (\s w -> s ++ " " ++ show w ++ ":Qbit") "Outputs:" outWires ++ "\n"


-- | Export a circuit to IR format.
-- Before the export, the circuit is 'reallocated' via a call to allocate (Circuits) that optimises the use of
-- wires.
export_to_IR :: Circuit -> IRDoc
export_to_IR circ =
  let (circ', _) = allocate circ in
  let irnew = new_with_inputs $ qIn circ' in
  let irgates = List.foldl (\irdoc g -> append_gate g irdoc) irnew $ gates circ' in
  append_outputs (qOut circ') irgates



