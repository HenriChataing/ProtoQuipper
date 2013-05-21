module Circuits where

import Data.List as List
import Data.Map as Map

import Classes

import Gates

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
  | Unary String Int
  | Binary String Int Int
    deriving Show

-- Some readdressing
readdress :: Gate -> Binding -> Gate
------------------------------------
readdress (Unary s q) b = Unary s (applyBinding b q)
readdress (Binary s qa qb) b = Binary s (applyBinding b qa) (applyBinding b qb)

instance Reversible Gate where
  rev (Init q b) = Term q b
  rev (Term q b) = Init q b
  rev (Unary s q) = case List.lookup s unaryRev of
                      Just s' -> Unary s' q
                      Nothing -> error ("Unary gate " ++ s ++ " has no defined inverse")
  rev (Binary s qa qb) = case List.lookup s binaryRev of
                           Just s' -> Binary s' qa qb
                           Nothing -> error ("Binary gate " ++ s ++ " has no defined inverse")

-- Apply a binding function to the addresses of a gate
---- The output is the resulting gate and a binding function from the old addresses to the new
instance Caps Gate where
  -- Normal gates
  unencap c g@(Unary _ _) b = (c { gates = (gates c) ++ [readdress g b] }, b)
  unencap c g@(Binary _ _ _) b = (c { gates = (gates c) ++ [readdress g b] }, b)
  -- Creation / deletion of wires
  unencap c (Term q bt) b = let q' = applyBinding b q in
    (c { gates = (gates c) ++ [Term q' bt], qOut = List.delete q' (qOut c) }, List.delete (q, q') b)
  unencap c (Init q bt) b = let q' = freshAddress (qOut c) in
    (c { gates = (gates c) ++ [Init q' bt], qOut = q':(qOut c) }, (q, q'):b)


-- Result of the printing
model :: Gate -> [(Int, String)]
model (Binary s qa qb) =
  let sym = case List.lookup s binarySym of
              Just sy -> sy
              Nothing -> error ("Binary gate " ++ s ++ " has no specified symbolic representation")
            in
  if qa < qb then
    (2 * qa, fst sym):(2 * qb, snd sym):(take (2 * qb - 2 * qa - 1) $ List.iterate (\(l, s) -> (l+1, s)) (2 * qa + 1, " | "))
  else
    (2 * qa, fst sym):(2 * qb, snd sym):(take (2 * qa - 2 * qb - 1) $ List.iterate (\(l, s) -> (l+1, s)) (2 * qb + 1, " | "))

model (Unary s q) =
  let sym = case List.lookup s unarySym of
              Just sy -> sy
              Nothing -> error ("Unary gate " ++ s ++ " has no specified symbolic representation")
            in
  [(2 * q, sym)]

model (Init q bt) =
  [(2 * q, show bt ++ "|-")]

model (Term q bt) =
  [(2 * q, "-|" ++ show bt)]

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
printGate g = do
  printMulti $ model g

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
