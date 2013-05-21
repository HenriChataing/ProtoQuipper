module Gates where

import Syntax

import Circuits
import Values

-- Basic gates types
gateTypes :: [(String, Type)]
------------------------------
gateTypes =
  [ ("H", TCirc TQBit TQBit),
    ("NOT", TCirc TQBit TQBit),
    ("S", TCirc TQBit TQBit),
    ("T", TCirc TQBit TQBit),
    ("Y", TCirc TQBit TQBit),
    ("Z", TCirc TQBit TQBit),
    ("INIT0", TCirc TUnit TQBit),
    ("INIT1", TCirc TUnit TQBit),
    ("TERM0", TCirc TQBit TUnit),
    ("TERM1", TCirc TQBit TUnit),
   
    ("SWAP", TCirc (TTensor TQBit TQBit) (TTensor TQBit TQBit)),
    ("CNOT", TCirc (TTensor TQBit TQBit) (TTensor TQBit TQBit)) ]

-- A set of basic gates, basis for an binding environment
gateValues :: [(String, Value)]
-------------------------------
gateValues =
  [ ("H",    VCirc (VQBit 0) (Circ { qIn = [0],
                                     gates = [ Had 0 ],
                                     qOut = [0] }) (VQBit 0)),
    ("CNOT", VCirc (VPair (VQBit 0) (VQBit 1)) (Circ { qIn = [0, 1],
                                                       gates = [ Cont (Not 0) 1 ],
                                                       qOut = [0, 1] }) (VPair (VQBit 0) (VQBit 1))),
    ("SWAP", VCirc (VPair (VQBit 0) (VQBit 1)) (Circ { qIn = [0, 1],
                                                       gates = [ Swap 0 1 ],
                                                       qOut = [0, 1] }) (VPair (VQBit 0) (VQBit 1))),
    ("NOT",  VCirc (VQBit 0) (Circ { qIn = [0],
                                     gates = [ Not 0 ],
                                     qOut = [0] }) (VQBit 0)),
    ("S", VCirc (VQBit 0) (Circ { qIn = [0],
                                  gates = [ S 0 ],
                                  qOut = [0] }) (VQBit 0)),
    ("T", VCirc (VQBit 0) (Circ { qIn = [0],
                                  gates = [ T 0 ],
                                  qOut = [0] }) (VQBit 0)),
    ("Y", VCirc (VQBit 0) (Circ { qIn = [0],
                                  gates = [ Y 0 ],
                                  qOut = [0] }) (VQBit 0)),
    ("Z", VCirc (VQBit 0) (Circ { qIn = [0],
                                  gates = [ Z 0 ],
                                  qOut = [0] }) (VQBit 0)),
    ("INIT0", VCirc VUnit (Circ { qIn = [],
                                   gates = [ Init 0 0 ],
                                   qOut = [0] }) (VQBit 0)),
    ("INIT1", VCirc VUnit (Circ { qIn = [],
                                   gates = [ Init 0 1 ],
                                   qOut = [0] }) (VQBit 0)),
    ("TERM0", VCirc (VQBit 0) (Circ { qIn = [0],
                                      gates = [ Term 0 0 ],
                                      qOut = [] }) VUnit),
    ("TERM1", VCirc (VQBit 0) (Circ { qIn = [0],
                                      gates = [ Term 0 1 ],
                                      qOut = [] }) VUnit) ]

