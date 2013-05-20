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
sym (IT _) = "[\x0305T]"
sym (IS _) = "[\x0305S]"

-- Line coverage of a gate
cover :: Gate -> [Int]
----------------------
cover (Cont g q) =
  let mn = min q (minimum $ cover g) in
  let mx = max q (maximum $ cover g) in
  take (mx-mn+1) $ iterate (+1) mn

cover g = [firstq g]

-- Result of the printing
model :: Gate -> [(Int, String)]
model (Cont g q) =
  let ls = model g in
  let mn = fst $ minimum $ ls in
  let mx = fst $ maximum $ ls in
  if mn <= 2 * q && 2 * q <= mx then
    List.map (\(l, s) -> if l == 2 * q then (l, "-*-") else (l, s)) ls
  else if 2 * q < mn then
    -- Vertical wire from 2q+1 to m-1, and -*- on 2q
    (2 * q, "-*-"):((take (mn - 2 * q - 1) $ iterate (\(l, s) -> (l+1, s)) (2 * q + 1, " | ")) ++ ls)
  else -- if mx < 2 * q
    -- Vertical wire from mx+1 to 2q-1, and -*- on 2q
    (2 * q, "-*-"):((take (2 * q - mx - 1) $ iterate (\(l, s) -> (l+1, s)) (mx + 1, " | ")) ++ ls)

model g = [(2 * firstq g, sym g)]

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

----------------------------------------------------
-- Wire allocation                                --
-- Each quantum address is associated with a wire --

-- Associate a wire to each quantum address
data Addressing = Address { wires :: Int,         -- Number of wires
                            unused :: [Int],      -- Unused wires
                            bind :: Binding }     -- Binding from addresses to wires
newtype AdState a = AdState (Addressing -> (Addressing, a))
instance Monad AdState where
  return a = AdState (\ad -> (ad, a))
  AdState run >>= action = AdState (\ad -> let (ad', a) = run ad in
                                           let AdState run' = action a in
                                           run' ad')

-- Find a unused wire and binds the qaddress to this wire
bindWire :: Int -> AdState Int
bindWire q = AdState (\ad -> case unused ad of
                               [] -> (ad { wires = (+1) $ wires ad,
                                           bind = (q, wires ad):(bind ad) }, wires ad)
                               w:cw -> (ad { unused = cw,
                                             bind = (q, w):(bind ad) }, w))
-- Assiocated wire
assocWire :: Int -> AdState Int
assocWire q = AdState (\ad -> (ad, case List.lookup q $ bind ad of
                                     Just w -> w
                                     Nothing -> error ("Unbound address " ++ show q)))

-- Associated gate   - Input gate can't be init or term
assocGate :: Gate -> AdState Gate
assocGate g = AdState (\ad -> (ad, readdress g $ bind ad))

-- Delete a wire
delWire :: (Int, Int) -> AdState ()
delWire (q, w) = AdState (\ad -> (ad { unused = w:(unused ad),
                                       bind = List.delete (q, w) $ bind ad }, ()))

-- Allocate all addresses  - Return te number of used lines too
stateAllocate :: [Gate] -> AdState [Gate]
allocate :: Circuit -> ([Gate], Int)
---------------------------------------
stateAllocate [] = do
  return []

stateAllocate (Init q bt:cg) = do
  w <- bindWire q
  cg' <- stateAllocate cg
  return (Init w bt:cg')

stateAllocate (Term q bt: cg) = do
  w <- assocWire q
  delWire (q, w)
  cg' <- stateAllocate cg
  return (Term w bt:cg')

stateAllocate (g:cg) = do
  g' <- assocGate g
  cg' <- stateAllocate cg
  return (g':cg')
 
allocate c =
  let AdState run = do
      stateAllocate $ gates c
  in
  let initState = List.foldl (\ad q -> ad { wires = (+1) $ wires ad,
                                            bind = (q, wires ad):(bind ad) })
                             (Address { wires = 0, unused = [], bind = []})
                             (qIn c) in
  let (ad, g) = run initState in
  (g, wires ad)

---------------------------------------------------------------------------------
-- Column filling                                                              --
-- Each gate is printed in a column, in a such a way as to minimize the number --
-- of columns                                                                  --

data Column = Col { chars :: Map Int String }

data Grid = Grid { gsize :: Int,               -- Number of lines
                   columns :: [Column] }       -- Reversed list of all columns
             
-- Look for the deepest column until which the line l is empty
freeDepth :: Int -> [Column] -> Int
freeDepth l [] = -1
freeDepth l (c:cl) = case Map.lookup l $ chars c of
                       Nothing -> 1 + (freeDepth l cl)
                       Just _ -> -1
 
-- Look for the deepest column until which all the lines l1 .. ln are empty
freeCommonDepth :: [Int] -> [Column] -> Int
freeCommonDepth ls c = List.minimum (List.map (\l -> freeDepth l c) ls)

-- Print at depth n
printAt :: Int -> Int -> String -> [Column] -> [Column]
printAt l 0 s (c:cl) = (c { chars = Map.insert l s $ chars c }:cl)
printAt l n s (c:cl) = c:(printAt l (n-1) s cl)

newtype GrState a = GrState (Grid -> (Grid, a))
instance Monad GrState where
  return a = GrState (\gr -> (gr, a))
  GrState run >>= action = GrState (\gr -> let (gr', a) = run gr in
                                           let GrState run' = action a in
                                           run' gr')

-- Print character in line n
printSingle :: Int -> String -> GrState ()
printSingle l s = GrState (\gr -> let d = freeDepth l $ columns gr in
                                  if d == -1 then
                                    let nc = Col { chars = Map.insert l s Map.empty } in
                                    (gr { columns = nc:(columns gr) }, ())
                                  else
                                    (gr { columns = printAt l d s $ columns gr }, ()))

-- Print n characters on the same line
printMulti :: [(Int, String)] -> GrState ()
printMulti ls = GrState (\gr -> let d = freeCommonDepth (fst $ unzip ls) $ columns gr in
                                if d == -1 then
                                  let nc = Col { chars = fromList ls } in
                                  (gr { columns = nc:(columns gr) }, ())
                                else
                                  (List.foldl (\gr (l, s) -> gr { columns = printAt l d s $ columns gr }) gr ls, ()))


-- Print a gate
printGate :: Gate -> GrState ()
printGate (Cont g q) = do
  printMulti $ model (Cont g q)
   
printGate g = do
  printSingle (2 * firstq g) (sym g)

-- Fill the gaps
outputLine :: Int -> GrState String
outputLine l = GrState (\gr -> (gr, let initMode =   case Map.lookup l $ chars $ last $ columns gr of
                                                        Just sym -> if isSuffixOf "|-" sym then ("   ", False)
                                                                    else if l `mod` 2 == 0 then ("---", True)
                                                                    else ("   ", False)
                                                        Nothing -> if l `mod` 2 == 0 then ("---", True) else ("   ", False)
                                                      in
                                                        
                                    let (s, _) = List.foldr (\c (s, on) -> 
                                                                let (ns, non) = case Map.lookup l $ chars c of
                                                                                  Just sm -> if isSuffixOf "|-" sm then
                                                                                               (s ++ sm, True)
                                                                                             else if isPrefixOf "-|" sm then
                                                                                               (s ++ sm, False)
                                                                                             else (s ++ sm, on)
                                                                                  Nothing -> if l `mod` 2 == 0 && on then (s ++ "---", on)
                                                                                             else (s ++ "   ", on)
                                                                in
                                                                -- Printing wires
                                                                if l `mod` 2 == 0 && non then
                                                                  (ns ++ "---", non)
                                                                else
                                                                  (ns ++ "   ", non)) initMode $ columns gr in
                                    s))

-- Output the whole grid
output :: GrState String
output = GrState (\gr -> let num = take (gsize gr) $ iterate (+1) 0 in
                         (gr, List.foldl (\s l -> let GrState run = do outputLine l in
                                                  let (_, ln) = run gr in
                                                  (s ++ ln ++ "\n")) "\n" num))

instance PPrint Circuit where
  pprint c =
    let (gates, lns) = allocate c in
    let runGr = GrState (\gr -> List.foldl (\(gr, _) g -> let GrState run = printGate g in
                                                          run gr) (gr, ()) gates) in
    let GrState run = (runGr >>= (\_ -> output)) in
    let (_, s) = run (Grid { gsize = 2 * lns - 1, columns = [] }) in
    s

  sprintn _ c = pprint c
  sprint c = pprint c
