module Circuits where

import Data.List as List
import Data.Map as Map

import Classes
import Utils

import Gates

-----------------------------------
-- Class of encapsulated objects --

class Caps a where
  unencap :: Circuit -> a -> Binding -> (Circuit, Binding)

-- Type of a binding
type Binding = [(Int, Int)]

-- Given the input of a circuit, pick up a new address
fresh_address :: [Int] -> Int
----------------------------
fresh_address [] = 0
fresh_address l = (maximum l) + 1

--------------------------

data Gate =
    Init Int Int
  | Term Int Int
  | Unary String Int
  | Binary String Int Int
  | Controlled Gate [Int]
    deriving Show

-- Some readdressing
readdress :: Gate -> Binding -> Gate
------------------------------------
readdress (Unary s q) b = Unary s (apply_binding b q)
readdress (Binary s qa qb) b = Binary s (apply_binding b qa) (apply_binding b qb)
readdress (Controlled g qlist) b = Controlled (readdress g b) (List.map (apply_binding b) qlist)

instance Reversible Gate where
  rev (Init q b) = Term q b
  rev (Term q b) = Init q b
  rev (Unary s q) = case List.lookup s unary_rev of
                      Just s' -> Unary s' q
                      Nothing -> error ("Unary gate " ++ s ++ " has no defined inverse")
  rev (Binary s qa qb) = case List.lookup s binary_rev of
                           Just s' -> Binary s' qa qb
                           Nothing -> error ("Binary gate " ++ s ++ " has no defined inverse")
  rev (Controlled g qlist) = Controlled (rev g) qlist

-- Apply a binding function to the addresses of a gate
---- The output is the resulting gate and a binding function from the old addresses to the new
instance Caps Gate where
  -- Normal gates
  unencap c g@(Unary _ _) b = (c { gates = (gates c) ++ [readdress g b] }, b)
  unencap c g@(Binary _ _ _) b = (c { gates = (gates c) ++ [readdress g b] }, b)
  unencap c (Controlled g qlist) b = (c { gates = (gates c) ++ [readdress (Controlled g qlist) b] }, b)
  -- Creation / deletion of wires
  unencap c (Term q bt) b = let q' = apply_binding b q in
    (c { gates = (gates c) ++ [Term q' bt], qOut = List.delete q' (qOut c) }, List.delete (q, q') b)
  unencap c (Init q bt) b = let q' = fresh_address (qOut c) in
    (c { gates = (gates c) ++ [Init q' bt], qOut = q':(qOut c) }, (q, q'):b)

-- Result of the printing
model :: Gate -> [(Int, String)]
model (Binary s qa qb) =
  let sym = case List.lookup s binary_sym of
              Just sy -> sy
              Nothing -> error ("Binary gate " ++ s ++ " has no specified symbolic representation")
            in
  if qa < qb then
    (2*qa, fst sym):(2*qb, snd sym):(List.map (\l -> (l, " | ")) [2*qa+1 .. 2*qb-1])
  else
    (2*qa, fst sym):(2*qb, snd sym):(List.map (\l -> (l, " | ")) [2*qb+1 .. 2*qa-1])

model (Unary s q) =
  let sym = case List.lookup s unary_sym of
              Just sy -> sy
              Nothing -> error ("Unary gate " ++ s ++ " has no specified symbolic representation")
            in
  [(2 * q, sym)]

model (Controlled g qlist) =
  let pg = model g in
  let (qmin, _) = List.minimum pg
      (qmax, _) = List.maximum pg in
  let (_, _, m) = List.foldl (\(qmn, qmx, mod) q ->
                               if 2*q < qmn then
                                 (2*q, qmx, (2*q, "-.-"):(List.map (\l -> (l, " | ")) [2*q+1 .. qmn-1] ++ mod))
                               else if qmx < 2*q then
                                 (qmn, 2*q, (2*q, "-.-"):(List.map (\l -> (l, " | ")) [qmx+1 .. 2*q-1] ++ mod))
                               else
                                 (qmn, qmx, List.map (\(l, s) -> if l == 2*q then (l, "-.-") else (l, s)) mod)) (qmin, qmax, pg) qlist in
  m

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
bind_wire :: Int -> AdState Int
bind_wire q = AdState (\ad -> case unused ad of
                               [] -> (ad { wires = (+1) $ wires ad,
                                           bind = (q, wires ad):(bind ad) }, wires ad)
                               w:cw -> (ad { unused = cw,
                                             bind = (q, w):(bind ad) }, w))
-- Assiocated wire
assoc_wire :: Int -> AdState Int
assoc_wire q = AdState (\ad -> (ad, case List.lookup q $ bind ad of
                                     Just w -> w
                                     Nothing -> error ("Unbound address " ++ show q)))

-- Associated gate   - Input gate can't be init or term
assoc_gate :: Gate -> AdState Gate
assoc_gate g = AdState (\ad -> (ad, readdress g $ bind ad))

-- Delete a wire
delete_vire :: (Int, Int) -> AdState ()
delete_vire (q, w) = AdState (\ad -> (ad { unused = w:(unused ad),
                                       bind = List.delete (q, w) $ bind ad }, ()))

-- Allocate all addresses  - Return te number of used lines too
state_allocate :: [Gate] -> AdState [Gate]
allocate :: Circuit -> ([Gate], Int)
---------------------------------------
state_allocate [] = do
  return []

state_allocate (Init q bt:cg) = do
  w <- bind_wire q
  cg' <- state_allocate cg
  return (Init w bt:cg')

state_allocate (Term q bt: cg) = do
  w <- assoc_wire q
  delete_vire (q, w)
  cg' <- state_allocate cg
  return (Term w bt:cg')

state_allocate (g:cg) = do
  g' <- assoc_gate g
  cg' <- state_allocate cg
  return (g':cg')
 
allocate c =
  let AdState run = do
      state_allocate $ gates c
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
free_depth :: Int -> [Column] -> Int
free_depth l [] = -1
free_depth l (c:cl) = case Map.lookup l $ chars c of
                       Nothing -> 1 + (free_depth l cl)
                       Just _ -> -1
 
-- Look for the deepest column until which all the lines l1 .. ln are empty
free_common_depth :: [Int] -> [Column] -> Int
free_common_depth ls c = List.minimum (List.map (\l -> free_depth l c) ls)

-- Print at depth n
print_at :: Int -> Int -> String -> [Column] -> [Column]
print_at l 0 s (c:cl) = (c { chars = Map.insert l s $ chars c }:cl)
print_at l n s (c:cl) = c:(print_at l (n-1) s cl)

newtype GrState a = GrState (Grid -> (Grid, a))
instance Monad GrState where
  return a = GrState (\gr -> (gr, a))
  GrState run >>= action = GrState (\gr -> let (gr', a) = run gr in
                                           let GrState run' = action a in
                                           run' gr')

-- Print n characters on the same line
print_multi :: [(Int, String)] -> GrState ()
print_multi ls = GrState (\gr -> let d = free_common_depth (fst $ unzip ls) $ columns gr in
                                if d == -1 then
                                  let nc = Col { chars = fromList ls } in
                                  (gr { columns = nc:(columns gr) }, ())
                                else
                                  (List.foldl (\gr (l, s) -> gr { columns = print_at l d s $ columns gr }) gr ls, ()))


-- Print a gate
print_gate :: Gate -> GrState ()
print_gate g = do
  print_multi $ model g

-- Fill the gaps
output_line :: Int -> GrState String
output_line l = GrState (\gr -> (gr, let initMode =   case Map.lookup l $ chars $ last $ columns gr of
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
output = GrState (\gr -> let num = [0 .. gsize gr - 1] in
                         (gr, List.foldl (\s l -> let GrState run = do output_line l in
                                                  let (_, ln) = run gr in
                                                  (s ++ ln ++ "\n")) "\n" num))

instance PPrint Circuit where
  pprint c =
    let (gates, lns) = allocate c in
    let runGr = GrState (\gr -> List.foldl (\(gr, _) g -> let GrState run = print_gate g in
                                                          run gr) (gr, ()) gates) in
    let GrState run = (runGr >>= (\_ -> output)) in
    let (_, s) = run (Grid { gsize = 2 * lns - 1, columns = [] }) in
    s ++ "\n"

  sprintn _ c = pprint c
  sprint c = pprint c
  genprint _ c _ = pprint c
