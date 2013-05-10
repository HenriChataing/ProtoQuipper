module Circuits where

import Data.List as List
import Data.Map as Map

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
  case List.lookup q b of
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
    (c { gates = (gates c) ++ [Term q' bt], qOut = List.delete q' (qOut c) }, List.delete (q, q') b)
  unencap c (Init q bt) b = let q' = freshAddress (qOut c) in
    (c { gates = (gates c) ++ [Init q' bt], qOut = q':(qOut c) }, (q, q'):b)
  -- Controlled gates
  unencap c (Cont g q) b = (c { gates = (gates c) ++ [readdress (Cont g q) b] }, b)



-- First wire of a gate
firstq :: Gate -> Int
---------------------
firstq (Init q _) = q
firstq (Term q _) = q
firstq (Cont _ q) = q
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

-- Line coverage of a gate
cover :: Gate -> [Int]
----------------------
cover (Cont g q) =
  let mn = min q (minimum $ cover g) in
  let mx = max q (maximum $ cover g) in
  take (mx-mn+1) $ iterate (+1) mn

cover g = [firstq g]

-----------------------

data Circuit = Circ {
  qIn :: [Int],
  qOut :: [Int],
  gates :: [Gate]
}

instance Show Circuit where
  show c = " " ++
    (List.foldl (\s i -> s ++ (show i) ++ " ") "" (qIn c)) ++ "[ " ++
    (List.foldl (\s g -> s ++ (show g) ++ " ") "" (gates c)) ++ "] " ++
    (List.foldl (\s i -> s ++ (show i) ++ " ") "" (qOut c))

instance Reversible Circuit where
  rev c =
    Circ {
      qIn = qOut c,
      qOut = qIn c,
      gates = List.map rev $ reverse $ gates c
    }

instance Caps Circuit where
  unencap c c' b =
    List.foldl (\(nc, b) g -> unencap nc g b) (c, b) (gates c')

-------------------------------
--- Circuit pretty printing ---


------------------------------------
-- Line manipulation and creation --

-- Create a padding of n white spaces
padding :: Int -> String
------------------------
padding n = replicate n ' '

-- used : is the line currently occupied
-- print : has the line been filled in the current column
-- num : line number
data LineSet = Set { ssize :: Int,               -- Number of lines in use
                     slines :: Map Int String,    -- physical lines
                     unused :: [Int],            -- Set of unused lines
                     currentColumn :: [Int],         -- Lines missing the current column
                     binding :: [(Int, Int)],    -- Binding from wires to lines
                     columnNumber :: Int }             -- Current column number

-- Create the initial bindings
initSet :: Circuit -> LineSet
-----------------------------
initSet c =
  let (b, ix) = List.foldl (\(l, ix) q -> ((q, ix):l, ix+2)) ([], 0) (qIn c) in
  let createlines = (\ix -> if ix == 0 then Map.insert 0 "" empty
                            else let m' = createlines (ix-1) in Map.insert ix "" m') in
  Set { ssize = ix-1,
        slines = createlines (ix-1),
        unused = [],
        currentColumn = take (ix-1) $ iterate (+1) 0,
        binding = b,
        columnNumber = 0 }

-- Find an unused line for the wire q, if there exists one
newLine :: LineSet -> Int -> (Int, LineSet)
----------------------------------------
newLine s@Set { unused = nsd, ssize = n, binding = b, slines = lns, columnNumber = c } q =
  case nsd of
  [] -> (n+1, s { ssize = n+2,
                  binding = (q, n+1):b,
                  slines = Map.insert (n+1) (padding c) $ Map.insert n (padding c) lns,
                  currentColumn = n:(n+1):(currentColumn s) })
  l:cl -> (l, s { binding = (q, l):b,
                  unused = cl })

-- If the n-th in the current column has been filled already
filled :: Int -> LineSet -> Bool
---------------------
filled n s =
  not (elem n $ currentColumn s)

-- If the line is alive
used :: Int -> LineSet -> Bool
------------------------------
used n s =
  not (elem n $ unused s)

-- Try printing the gate in the current column
-- The return value includes : if the gate was printed, changes made to the lineSet, and the gate with the binding applied
tryPrint :: LineSet -> Gate -> (Bool, LineSet, Gate)
------------------------------------------------------
tryPrint s g@(Init q bt)  = 
  let (nq, s') = newLine s q in
  let ng = Init nq bt in
  if filled nq s' then
    (False, (s' { unused = nq:(unused s') }), ng)
  else
    (True, pprintGate ng s', ng)
  
tryPrint s g@(Term q bt) =
  let nq = applyBinding (binding s) q in
  let s' = s { binding = List.delete (q, nq) $ binding s } in
  let ng = Term nq bt in
  if filled nq s' then
    (False, s', ng)
  else
    (True, pprintGate ng s', ng)
 
tryPrint s g =
  let ng = readdress g (binding s) in
  let cov = cover ng in
  if List.foldl (\v n -> v && (elem n $ currentColumn s)) True cov then
    (True, pprintGate ng s, ng)
  else
    (False, s, ng)

-------------------------------
-- Actual printing functions --

-- Appends a wire on the lines matching quantum addresses, spaces othewise
printWire :: LineSet -> LineSet
-------------------------------
printWire s = s { slines = mapWithKey (\n l ->
                                        if n `mod` 2 == 0 && used n s then
                                          l ++ "---" 
                                        else
                                          l ++ "   ") $ slines s,
                  columnNumber = (columnNumber s)+3 }

-- Actual printing
pprintGate :: Gate -> LineSet -> LineSet

-- Init gates
-- Need to intercept this gate : the wire is removed from unused lines only after it has been printed
pprintGate g@(Init nq _) s =
  s { slines = case Map.lookup nq $ slines s of
              Just l -> Map.insert nq (l ++ sym g) $ slines s
              Nothing -> error ("Shouldn't happen : undefined line " ++ show nq),
      currentColumn = List.delete nq $ currentColumn s,
      unused = List.delete nq (unused s) }

-- Terl gates
-- Need to intercept this gate : the wire is added to unused lines only after it has been printed
pprintGate g@(Term nq _) s =
  s { slines = case Map.lookup nq $ slines s of
              Just l -> Map.insert nq (l ++ sym g) $ slines s
              Nothing -> error ("Shouldn't happen : undefined line " ++ show nq),
      currentColumn = List.delete nq $ currentColumn s,
      unused = nq:(unused s) }

-- Controlled gates
pprintGate (Cont g q) s =
  let s' = pprintGate g s in
  let q' = firstq g in
  let (mn, mx) = if q' < q then (q', q) else (q, q') in
  let s'' = List.foldl (\s n -> if filled n s then
                                  s
                                else
                                  s { slines = case Map.lookup n $ slines s of
                                               -- Printing of vertical wires
                                               Just l -> Map.insert n (if n `mod` 2 == 0 && used n s then
                                                                         l ++ "-|-"
                                                                       else
                                                                         l ++ " | ") $ slines s
                                               Nothing -> error ("Shouldn't happen : undefined line " ++ show n),
                                      currentColumn = List.delete n $ currentColumn s }) s' (take (mx-mn-1) $ iterate (+1) (mn+1)) in
  s'' { slines = case Map.lookup q $ slines s'' of
                 Just l -> Map.insert q (l ++ "-*-") $ slines s''
                 Nothing -> error ("Shouldn't happen : undefined line " ++ show q),
        currentColumn = List.delete q $ currentColumn s'' }

-- Other gates
pprintGate g s =
  let nq = firstq g in
  s { slines = case Map.lookup nq $ slines s of
              Just l -> Map.insert nq (l ++ sym g) $ slines s
              Nothing -> error ("Shouldn't happen : undefined line " ++ show nq),
      currentColumn = List.delete nq $ currentColumn s }


-- Complete the current column by filling the missing lines
complete :: LineSet -> LineSet
------------------------------
complete s =
  List.foldl (\s n -> case Map.lookup n $ slines s of
                      Just l -> if n `mod` 2 == 0 && used n s then
                                  s { slines = Map.insert n (l ++ "---") $ slines s }
                                else
                                  s { slines = Map.insert n (l ++ "   ") $ slines s }
                      Nothing -> error ("Shouldn't happen : undefined line " ++ show n)
             ) (s { currentColumn = take (ssize s) $ iterate (+1) 0,
                    columnNumber = (columnNumber s)+3 }) (currentColumn s)

-- Plug the lines together
build :: LineSet -> String
--------------------------
build s =
  List.foldl (\text n -> case Map.lookup n $ slines s of
                         Just l -> text ++ l ++ "\n"
                         Nothing -> error ("Shouldn't happen : undefined line " ++ show n)
             ) "" (take (ssize s) $ iterate (+1) 0)

-- Print all the gates, putting as much as possible on one column
pprintAll :: [Gate] -> LineSet -> LineSet
-----------------------------------------
pprintAll [] s =
  (complete s)

pprintAll (g:cg) s =
  let (feat, s', g') = tryPrint s g in
  if feat then
    pprintAll cg s'
  else
    let cs = printWire $ complete s' in
    let cs' = pprintGate g' cs in
    pprintAll cg cs'

-- Printing function
pprintCircuit :: Circuit -> String
----------------------------------
pprintCircuit c =
  -- Mapping from quantum addresses to lines
  let nset = printWire $ initSet c in
  -- Building the lines
  let cset = pprintAll (gates c) nset in
  build $ printWire cset
