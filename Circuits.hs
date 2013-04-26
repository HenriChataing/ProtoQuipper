module Circuits where

-- Application of a binding function
-- Missing addresses are applied the identity function
applyBinding :: [(Int, Int)] -> Int -> Int
applyBinding b q =
  case lookup q b of
    Just q' -> q'
    Nothing -> q 

--- Class definitions ---
class Reversible a where
  rev :: a -> a

class Addressed a where
  readdress :: [(Int, Int)] -> a ->(a, [(Int, Int)])
--------------------------

data Gate =
    Not Int
  | Hadamard Int
  | CNot Int Int
  | S Int
  | IS Int
  | T Int
  | IT Int
    deriving Show

instance Reversible Gate where
  rev (Not q) = Not q
  rev (Hadamard q) = Hadamard q
  rev (CNot q1 q2) = CNot q1 q2
  rev (S q) = IS q
  rev (IS q) = S q
  rev (T q) = IT q
  rev (IT q) = T q

-- Apply a binding function to the addresses of a gate
---- The output is the resulting gate and a binding function from the old addresses to the new
instance Addressed Gate where
  readdress b (Not q) = (Not (applyBinding b q), [(q, applyBinding b q)])
  readdress b (Hadamard q) = (Hadamard (applyBinding b q), [(q, applyBinding b q)])
  readdress b (CNot q1 q2) = (CNot (applyBinding b q1) (applyBinding b q2), [(q1, applyBinding b q1), (q2, applyBinding b q2)])
  readdress b (S q) = (S (applyBinding b q), [(q, applyBinding b q)])
  readdress b (IS q) = (IS (applyBinding b q), [(q, applyBinding b q)])
  readdress b (T q) = (T (applyBinding b q), [(q, applyBinding b q)])
  readdress b (IT q) = (IT (applyBinding b q), [(q, applyBinding b q)])

-----------------------

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

instance Reversible Circuit where
  rev c =
    Circ {
      qIn = qOut c,
      qOut = qIn c,
      gates = map rev $ reverse $ gates c
    }

instance Addressed Circuit where
  readdress b c =
    let c' = Circ {
      qIn = map (applyBinding b) (qIn c),
      qOut = map (applyBinding b) (qOut c),
      gates = map (fst . readdress b) (gates c)
    } in
    (c', zip (qOut c) (qOut c'))

-- Append a circuit, connection is given by a binding function
unencap :: [(Int, Int)] -> Circuit -> Circuit -> (Circuit, [(Int, Int)])
unencap b c d =
  let (d', b') = readdress b d in
  (Circ {
     qIn = qIn c,
     qOut = qOut c, -- In fact (qOut c \ qIn q) U qOut d
     gates = (gates c) ++ (gates d')
   }, b')
