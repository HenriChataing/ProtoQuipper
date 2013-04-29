module Circuits where

import Data.List

-- Type of a binding
type Binding = [(Int, Int)]

-- Application of a binding function
-- Missing addresses are applied the identity function
applyBinding :: [(Int, Int)] -> Int -> Int
applyBinding b q =
  case lookup q b of
    Just q' -> q'
    Nothing -> q 

-- Given the input of a circuit, pick up a new address
freshAddress :: [Int] -> Int
freshAddress [] = 0
freshAddress l = (maximum l) + 1

--- Class definitions ---
class Reversible a where
  rev :: a -> a

class Caps a where
  unencap :: Circuit -> a -> Binding -> (Circuit, Binding)

--------------------------

data Gate =
    New Int
  | Del Int
  | Not Int
  | Had Int
  | S Int
  | IS Int
  | T Int
  | IT Int
  | Cont Gate Int
    deriving Show

-- Some readdressing
readdress :: Gate -> Binding -> Gate
readdress (Not q) b = Not (applyBinding b q)
readdress (Had q) b = Had (applyBinding b q)
readdress (S q) b = S (applyBinding b q)
readdress (IS q) b = IS (applyBinding b q)
readdress (T q) b = T (applyBinding b q)
readdress (IT q) b = IT (applyBinding b q)
readdress (Cont g q) b = Cont (readdress g b) (applyBinding b q)

instance Reversible Gate where
  rev (Not q) = Not q
  rev (Had q) = Had q
  rev (S q) = IS q
  rev (IS q) = S q
  rev (T q) = IT q
  rev (IT q) = T q
  rev (Cont g c) = Cont (rev g) c

-- Apply a binding function to the addresses of a gate
---- The output is the resulting gate and a binding function from the old addresses to the new
instance Caps Gate where
  -- Normal gates
  unencap c (Not q) b = (c { gates = (gates c) ++ [readdress (Not q) b] }, b)
  unencap c (Had q) b = (c { gates = (gates c) ++ [readdress (Had q) b] }, b)
  unencap c (S q) b = (c { gates = (gates c) ++ [readdress (S q) b] }, b)
  unencap c (IS q) b = (c { gates = (gates c) ++ [readdress (IS q) b] }, b)
  unencap c (T q) b = (c { gates = (gates c) ++ [readdress (T q) b] }, b)
  unencap c (IT q) b = (c { gates = (gates c) ++ [readdress (IT q) b] }, b)
  -- Creation / deletion of wires
  unencap c (Del q) b = let q' = applyBinding b q in
    (c { gates = (gates c) ++ [Del q'], qOut = delete q' (qOut c) }, delete (q, q') b)
  unencap c (New q) b = let q' = freshAddress (qOut c) in
    (c { gates = (gates c) ++ [New q'], qOut = q':(qOut c) }, (q, q'):b)
  -- Controlled gates
  unencap c (Cont g q) b = (c { gates = (gates c) ++ [readdress (Cont g q) b] }, b)



-- First wire of a gate
firstq :: Gate -> Int
firstq (Not q) = q
firstq (Had q) = q
firstq (S q) = q
firstq (T q) = q
firstq (IS q) = q
firstq (IT q) = q

sym :: Gate -> String
sym (Not _) = "X"
sym (Had _) = "H"
sym (T _) = "T"
sym (S _) = "S"
sym (IT _) = "t\x0305"
sym (IS _) = "s\x0305"

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

instance Caps Circuit where
  unencap c c' b =
    foldl (\(nc, b) g -> unencap nc g b) (c, b) (gates c')

-------------------------------
--- Circuit pretty printing ---

-- Creates n lines
buildLines :: Int -> [(Int, String)]
buildLines 0 = [(0, "")]
buildLines n = (buildLines (n-1)) ++ [(n, "")]

-- Create a new line
newLine :: [(Int, String)] -> (Int, [(Int, String)])
newLine ln =
  let (n, s) = last ln in
  -- When a wire is deleted, its line number is changed to n+1, so that the last used number is still accessible
  let nn = n - n `mod` 2 in
  -- A white padding is added to match the current line length
  let pad = replicate (length s) ' ' in
  (nn+2, ln ++ [(nn+1, pad), (nn+2, pad)])

-- Appends a wire on the lines matching quantum addresses, spaces othewise
printWire :: [(Int, String)] -> [(Int, String)]
printWire = map (\(n, s) -> if n `mod` 2 == 0 then (n, s++"---") else (n, s++"   "))

-- Given a binding from addresses to lines, print the next gates
pprintGate :: Binding -> Gate -> [(Int, String)] -> ([(Int, String)], Binding)
  -- Creation / deletion of wires
pprintGate b (New q) ln =
  let (nq, lnq) = newLine ln in
  (map (\(n, s) -> if n == nq then             (n, s ++ "[")
                   else if n `mod` 2 == 0 then (n, s ++ "-")
                   else                        (n, s ++ " ")) lnq, (q, nq):b)

pprintGate b (Del q) ln =
  let nq = applyBinding b q in
  (map (\(n, s) -> if n == nq then              (n+1, s ++ "]")   -- The line number is changed to be odd
                   else if n `mod` 2 == 0 then  (n, s ++ "-")
                   else                         (n, s ++ " ")) ln, delete (q, nq) b)
  -- Controlled gates
pprintGate b (Cont g q) ln =
  let nq1 = applyBinding b q in
  let nq2 = applyBinding b (firstq g) in
  (map (\(n, s) -> if n == nq1 then                                (n, s ++ "*")
                  else if n == nq2 then                            (n, s ++ (sym g))
                  else if (nq1 < nq2) && (nq1 < n && n < nq2) then (n, s ++ "|")
                  else if (nq2 < nq1) && (nq2 < n && n < nq1) then (n, s ++ "|")
                  else if n `mod` 2 == 0 then                      (n, s ++ "-")
                  else                                             (n, s ++ " ")) ln, b)
  -- Normal gates
pprintGate b g ln =
  (map (\(n, s) -> if n == (applyBinding b (firstq g)) then (n, s ++ (sym g))
                   else if n `mod` 2 == 0 then                   (n, s ++ "-")
                   else                                     (n, s ++ " ")) ln, b)

pprintCircuit :: Circuit -> String
pprintCircuit c =
  -- Mapping from quantum addresses to lines
  let (b, ix) = foldl (\(l, ix) q -> (l ++ [(q, ix)], ix+2)) ([], 0) (qIn c) in
  -- Building the lines
  let lines = printWire $ buildLines (ix-2) in
  -- Print the gates
  let (all, _) = foldl (\(l, b) g -> let (nl, nb) = pprintGate b g l in
                                     (printWire nl, nb)) (lines, b) (gates c) in
  foldl (\s (n, l) -> s ++ l ++ "\n") "" all



