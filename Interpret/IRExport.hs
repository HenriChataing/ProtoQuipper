-- | This module defines a tool for exporting circuits to the Intermediate Representation. The main function, 'export_to_IR', inputs a circuit (defined in module "Interpret.Circuits")
-- and outputs a string that contains the IR specification of the circuit.
module Interpret.IRExport where

import Interpret.Circuits

import qualified Data.List as List


-- | The type of IR document files.
type IRDoc = String


-- | Create a new IR document, initialized with the input wires.
new_with_inputs :: [Int] -> IRDoc
new_with_inputs [] =
  "Inputs: none\n"

new_with_inputs (w:wires) =
  let irdoc = List.foldl (\irdoc w -> irdoc ++ ", " ++ show w ++ ":Qbit") ("Inputs: " ++ show w ++ ":Qbit") wires in
  irdoc ++ "\n"
 

-- | Append a single gate to the specification.
append_gate :: Gate -> IRDoc -> IRDoc
-- Init and term
append_gate (Init b w) irdoc = irdoc ++ "QInit" ++ show b ++ "(" ++ show w ++ ")\n"
append_gate (Term b w) irdoc = irdoc ++ "QTerm" ++ show b ++ "(" ++ show w ++ ")\n"

-- Unary gates
-- Some gates have a specific format in IR
append_gate (Phase n w) irdoc =
  irdoc ++ "QRot[\"R(2pi/%)\"," ++ show (fromIntegral (2*n) :: Float) ++ "](" ++ show w ++ ")\n" 
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
                     "GATE_EITZ" -> ("exp(-itZ)", "")
                     "GATE_EITZ_INV" -> ("exp(-itZ)", "*")
    in
  irdoc ++ "QGate[\"" ++ prg ++ "\"]" ++ inv ++ "(" ++ show w ++ ")\n" 

-- Binary gates
append_gate (Binary "CNOT" w0 w1) irdoc =
  irdoc ++ "QGate[\"not\"](" ++ show w0 ++ ") with controls=[+" ++ show w1 ++ "]\n"
append_gate (Binary "SWAP" w0 w1) irdoc =
  irdoc ++ "QGate[\"swap\"](" ++ show w0 ++ ", " ++ show w1 ++ ")\n"
append_gate (Binary "GATE_W" w0 w1) irdoc =
  irdoc ++ "QGate[\"W\"](" ++ show w0 ++ ", " ++ show w1 ++ ")\n"

-- Controlled gates
append_gate (Controlled g (c:rest)) irdoc =
  let prg = append_gate g "" in
  irdoc ++ List.init prg ++ " with controls=[" ++ show_ctrl c ++ List.foldl (\s w -> s ++ ", " ++ show_ctrl w) "" rest ++"]\n"
  where
    show_ctrl (w,sign) = (if sign then "+" else "-") ++ show w


-- | Add the list of output wires to the document.
append_outputs :: [Int] -> IRDoc -> IRDoc
append_outputs [] irdoc =
  irdoc ++ "Outputs: none\n"

append_outputs (w:wires) irdoc =
  irdoc ++ List.foldl (\s w -> s ++ ", " ++ show w ++ ":Qbit") ("Outputs: " ++ show w ++ ":Qbit") wires ++ "\n"


-- | Export a circuit to IR format.
-- Before the export, the circuit is reallocated via a call to 'Interpret.Circuits.allocate' that optimizes the use of
-- wires.
export_to_IR :: Circuit -> IRDoc
export_to_IR circ =
  let (circ', _) = allocate circ in
  let irnew = new_with_inputs $ qIn circ' in
  let irgates = List.foldl (\irdoc g -> append_gate g irdoc) irnew $ gates circ' in
  append_outputs (qOut circ') irgates



