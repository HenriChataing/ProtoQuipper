module Circuits where

import Data.List

import Classes

-----------------------------------
-- Class of encapsulated objects --

class Caps a where
  unencap :: Circuit -> a -> Binding -> (Circuit, Binding)


-- Type of a binding
type Binding = [(Int, Int)]

-- Application of a binding function
-- Missing addresses are applied the identity function
applyBinding :: [(Int, Int)] -> Int -> Int
------------------------------------------
applyBinding b q =
  case lookup q b of
    Just q' -> q'
    Nothing -> q 

-- Given the input of a circuit, pick up a new address
freshAddress :: [Int] -> Int
----------------------------
freshAddress [] = 0
freshAddress l = (maximum l) + 1

--------------------------

data Gate =
    Init Int Int
  | Term Int Int
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
------------------------------------
readdress (Not q) b = Not (applyBinding b q)
readdress (Had q) b = Had (applyBinding b q)
readdress (S q) b = S (applyBinding b q)
readdress (IS q) b = IS (applyBinding b q)
readdress (T q) b = T (applyBinding b q)
readdress (IT q) b = IT (applyBinding b q)
readdress (Cont g q) b = Cont (readdress g b) (applyBinding b q)

instance Reversible Gate where
  rev (Init q b) = Term q b
  rev (Term q b) = Init q b
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
  unencap c (Term q bt) b = let q' = applyBinding b q in
    (c { gates = (gates c) ++ [Term q' bt], qOut = delete q' (qOut c) }, delete (q, q') b)
  unencap c (Init q bt) b = let q' = freshAddress (qOut c) in
    (c { gates = (gates c) ++ [Init q' bt], qOut = q':(qOut c) }, (q, q'):b)
  -- Controlled gates
  unencap c (Cont g q) b = (c { gates = (gates c) ++ [readdress (Cont g q) b] }, b)



-- First wire of a gate
firstq :: Gate -> Int
---------------------
firstq (Not q) = q
firstq (Had q) = q
firstq (S q) = q
firstq (T q) = q
firstq (IS q) = q
firstq (IT q) = q

-- Symbolic representation of a gate
sym :: Gate -> String
---------------------
sym (Init _ b) = (show b) ++ "|-"
sym (Term _ b) = "-|" ++ (show b)
sym (Not _) = "[X]"
sym (Had _) = "[H]"
sym (T _) = "[T]"
sym (S _) = "[S]"
sym (IT _) = "[T\x0305]"
sym (IS _) = "[S\x0305]"

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

data Line = Line { num :: Int, string :: String, used :: Bool }

-- Creates n empty lines
buildLines :: Int -> [Line]
---------------------------
buildLines 0 = [ Line { num = 0, string = "", used = True } ]
buildLines n = (buildLines (n-1)) ++ [ Line { num = n, string = "", used = True } ]

-- Find an unused line, if there exists one
findEmptyLine :: [Line] -> (Int, [Line])
----------------------------------------
findEmptyLine [] = (-1, [])
findEmptyLine (l:cl) =
  if used l then
    let (id, cl') = findEmptyLine cl in (id, l:cl')
  else
    (num l, (l { used = True}):cl)

-- Claim an empty line, if possible, else create a new one
newLine :: [Line] -> (Int, [Line])
----------------------------------
newLine ln =
  let (n, ln') = findEmptyLine ln in
  if n == -1 then
    let l = last ln in
    -- A white padding is added to match the current line length
    let pad = replicate (length $ string l) ' ' in
    ((num l)+ 2, ln ++ [ Line { num = (num l)+1, string = pad, used = True },
                        Line { num = (num l)+2, string = pad, used = True } ])
  else
    (n, ln')

-- Appends a wire on the lines matching quantum addresses, spaces othewise
printWire :: [Line] -> [Line]
-----------------------------
printWire = map (\l@Line { num = n, string = s, used = u } ->
                    if n `mod` 2 == 0 && u then
                      l { string = s ++ "---" }
                    else
                      l { string = s ++ "   " })

-- Given a binding from addresses to lines, print the next gates
pprintGate :: Binding -> Gate -> [Line] -> ([Line], Binding)

  -- Creation / deletion of wires
pprintGate b (Init q bt) ln =
  let (nq, lnq) = newLine ln in
  (map (\l@Line { num = n, string = s, used = u } ->
                   if n == nq then                  l { string = s ++ (sym (Init q bt)) }
                   else if n `mod` 2 == 0 && u then l { string = s ++ "---" }
                   else                             l { string = s ++ "   " }) lnq, (q, nq):b)

pprintGate b (Term q bt) ln =
  let nq = applyBinding b q in
  (map (\l@Line { num = n, string = s, used = u } ->
                   if n == nq then                  l { string = s ++ (sym(Term q bt)), used = False }   -- The line number is changed to be odd
                   else if n `mod` 2 == 0 && u then l { string = s ++ "---" }
                   else                             l { string = s ++ "   " }) ln, delete (q, nq) b)
  -- Controlled gates
pprintGate b (Cont g q) ln =
  let nq1 = applyBinding b q in
  let nq2 = applyBinding b (firstq g) in
  (map (\l@Line { num = n, string =s, used = u } ->
                  if n == nq1 then                                 l { string = s ++ "-*-" }
                  else if n == nq2 then                            l { string = s ++ (sym g) }
                  else if (nq1 < nq2) && (nq1 < n && n < nq2) then l { string = s ++ " | " }
                  else if (nq2 < nq1) && (nq2 < n && n < nq1) then l { string = s ++ " | " }
                  else if n `mod` 2 == 0 && u then                 l { string = s ++ "---" }
                  else                                             l { string = s ++ "   " }) ln, b)
  -- Normal gates
pprintGate b g ln =
  (map (\l@Line { num = n, string = s, used = u } ->
                   if n == (applyBinding b (firstq g)) then l { string = s ++ (sym g) }
                   else if n `mod` 2 == 0 && u then         l { string = s ++ "---" }
                   else                                     l { string = s ++ "   " }) ln, b)

-- Printing function
pprintCircuit :: Circuit -> String
----------------------------------
pprintCircuit c =
  -- Mapping from quantum addresses to lines
  let (b, ix) = foldl (\(l, ix) q -> ((q, ix):l, ix+2)) ([], 0) (qIn c) in
  -- Building the lines
  let lines = printWire $ buildLines (ix-2) in
  -- Print the gates
  let (all, _) = foldl (\(l, b) g -> let (nl, nb) = pprintGate b g l in
                                     (printWire nl, nb)) (lines, b) (gates c) in
  foldl (\s l -> s ++ string l ++ "\n") "\n" all

