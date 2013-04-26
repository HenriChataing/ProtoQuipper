module Circ where

data Gate =
    Not Int
  | Hadamard Int
  | CNot Int Int
    deriving Show

data Circuit = Circ {
  qIn :: [Int],
  qOut :: [Int],
  gates :: [Gate]
}

instance Show Circuit where
  show c = " " ++
    (foldl (\s i -> s ++ (show i) ++ " ") "" (qIn c)) ++ "[ " ++
    (foldl (\s g -> s ++ (show g) ++ " ") "" (gates c)) ++ "] " ++
    (foldl (\s i -> s ++ (show i) ++ " ") "" (qOut c))

-- Application of a binding function
-- Missing addresses are applied the identity function
applyBinding :: [(Int, Int)] -> Int -> Int
applyBinding b q =
  case lookup q b of
    Just q' -> q'
    Nothing -> q 

-- Rename the addresses of a circuit in respect of a binding function
-- The output is the modified circuit, and a binding from the old output addresses to the new
readdressGate :: [(Int, Int)] -> Gate -> Gate
readdressGate b (Not q) = Not (applyBinding b q)
readdressGate b (Hadamard q) = Hadamard (applyBinding b q)
readdressGate b (CNot q1 q2) = CNot (applyBinding b q1) (applyBinding b q2)

readdressCircuit :: [(Int, Int)] -> Circuit -> (Circuit, [(Int, Int)])
readdressCircuit b c =
  let c' = Circ {
    qIn = map (applyBinding b) (qIn c),
    qOut = map (applyBinding b) (qOut c),
    gates = map (readdressGate b) (gates c)
  } in
  (c', zip (qOut c) (qOut c'))

-- Reverse a circuit
rev :: Circuit -> Circuit
rev c =
  Circ {
    qIn = qOut c,
    qOut = qIn c,
    gates = reverse $ gates c
  }

-- Append a circuit, in respect of a binding function
unencap :: [(Int, Int)] -> Circuit -> Circuit -> (Circuit, [(Int, Int)])
unencap b c d =
  let (d', b') = readdressCircuit b d in
  (Circ {
     qIn = qIn c,
     qOut = qOut c, -- In fact (qOut c \ qIn q) U qOut d
     gates = (gates c) ++ (gates d')
   }, b')
