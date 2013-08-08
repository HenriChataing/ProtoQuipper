-- | All about working with circuits. Includes the definition of the basic
-- circuit gates, the data type definition of a circuit along with all the semantic
-- operations such as encapsulating, printing...
module Interpret.Circuits where

import Data.List as List
import Data.Map as Map

import Classes


-- | List of unary gates.
-- Unary gates are defined by : their name, the name of the reversed gate, the symbol to use to represent it in
-- the display of the circuit (three chars).
unary_gates :: [(String, (String, String))]
unary_gates =
  [ ("GATE_H", ("GATE_H", "[H]")),
    ("NOT", ("NOT", "(+)")),
    ("GATE_X", ("GATE_X", "(+)")),
    ("GATE_Y", ("GATE_Y", "[Y]")),
    ("GATE_Z", ("GATE_Z", "[Z]")),
    ("GATE_S", ("GATE_S_INV", "[S]")),
    ("GATE_S_INV", ("GATE_S", "[\x0305S]")),
    ("GATE_T", ("GATE_T_INV", "[T]")),
    ("GATE_T_INV", ("GATE_T", "[\x0305T]")),
    ("GATE_E", ("GATE_E_INV", "[E]")),
    ("GATE_E_INV", ("GATE_E", "[E]")),
    ("GATE_OMEGA", ("GATE_OMEGA", "[\x03C9]")),
    ("GATE_V", ("GATE_V_INV", "[V]")),
    ("GATE_V_INV", ("GATE_V", "[\x0305V]")) ]


-- | List of binary gates.
-- The definition of a binary gate is similar to that of a unary one, but for the symbolic
-- representation which now takes two characters, one for each wire.
binary_gates :: [(String, (String, (String, String)))]
binary_gates =
  [ ("SWAP", ("SWAP", ("-X-", "-X-"))),
    ("CNOT", ("CNOT", ("(+)", "-*-"))),
    ("GATE_W", ("GATE_W", ("-W-", "-W-"))) ]



-- | Class of objects that can be unencapsulated, typically
-- gates and circuits.
class Caps a where
  unencap :: Circuit -> a -> Binding -> (Circuit, Binding)


-- | A binding is defined as a list of mappings q |-> q'.
type Binding = [(Int, Int)]


-- | Binding application. The binding function behaves as the identity function
-- on the addresses not in the mapping list.
apply_binding :: [(Int, Int)] -> Int -> Int
apply_binding b a =
  case List.lookup a b of
  Just a' -> a'
  Nothing -> a


-- | Given the input of a circuit, select an new unused address.
fresh_address :: [Int] -> Int
fresh_address [] = 0
fresh_address l = (maximum l) + 1


-- | Definition of the basic gates
data Gate =
    Init Int Int            -- ^ The initializers  0|-  and  1|-  are treated as gates.
  | Term Int Int            -- ^ Same thing : gates  -|0  and  -|1.
  | Phase Int Int           -- ^ The phase gate, with a rotation by Pi / n.
  | Unary String Int        -- ^ Unary gates. The first argument is the gate name, one of the list unary_gates defined above.
  | Binary String Int Int   -- ^ Binary gates. The first argument is the gate name, one of the list binary_gates.
  | Controlled Gate [Int]   -- ^ Controlled gates. The second argument is a list of control wires, not necessarily linear.
    deriving Show


-- | Readdressing of a gate : more specifically, applies the provided binding to the input and output of the gate.
readdress :: Gate -> Binding -> Gate
readdress (Phase n q) b = Phase n (apply_binding b q)
readdress (Unary s q) b = Unary s (apply_binding b q)
readdress (Binary s qa qb) b = Binary s (apply_binding b qa) (apply_binding b qb)
readdress (Controlled g qlist) b = Controlled (readdress g b) (List.map (apply_binding b) qlist)


-- | Gates are reversible objects. The reverse function uses the definition of the unary / binary gates
-- to know the name of the reversed gate.
instance Reversible Gate where
  -- Init and term are mutual inverses
  rev (Init q b) = Term q b
  rev (Term q b) = Init q b

  -- Othe gates
  rev (Phase n q) = Phase (-n) q
  rev (Unary s q) = case List.lookup s unary_gates of
                      Just (s', _) -> Unary s' q
                      Nothing -> error $ "Undefined unary gate " ++ s

  rev (Binary s qa qb) = case List.lookup s binary_gates of
                           Just (s', _) -> Binary s' qa qb
                           Nothing -> error $ "Undefined binary gate " ++ s

  -- The inverse of a controlled gate is the controlled inverse of the gate
  rev (Controlled g qlist) = Controlled (rev g) qlist


-- | Define the unencapsulating of a gate. The wires of the gate are renamed to match the wires to which the gate is
-- to be appended, and then the gate is added to the list of gates of the circuit. 
instance Caps Gate where
  -- Normal gates
  unencap c g@(Phase _ _) b = (c { gates = (gates c) ++ [readdress g b] }, b)
  unencap c g@(Unary _ _) b = (c { gates = (gates c) ++ [readdress g b] }, b)
  unencap c g@(Binary _ _ _) b = (c { gates = (gates c) ++ [readdress g b] }, b)
  unencap c (Controlled g qlist) b = (c { gates = (gates c) ++ [readdress (Controlled g qlist) b] }, b)

  -- Creation / deletion of wires
  unencap c (Term q bt) b = let q' = apply_binding b q in
    (c { gates = (gates c) ++ [Term q' bt], qOut = List.delete q' (qOut c) }, List.delete (q, q') b)
  unencap c (Init q bt) b = let q' = fresh_address (qOut c) in
    (c { gates = (gates c) ++ [Init q' bt], qOut = q':(qOut c) }, (q, q'):b)


-- | Display the gate on one column, and return the result as a list of associations
-- (line number, output). The wires are placed on even line numbers, and odd line numbers correspond
-- to gaps between lines (ie the wire addresses are multiplied by 2, and additional lines are created to fill the odd line numbers).
model :: Gate -> [(Int, String)]
model (Binary s qa qb) =
  let sym = case List.lookup s binary_gates of
              Just (_, sy) -> sy
              Nothing -> error $ "Undefined binary gate " ++ s
            in
  if qa < qb then
    (2*qa, fst sym):(2*qb, snd sym):(List.map (\l -> (l, " | ")) [2*qa+1 .. 2*qb-1])
  else
    (2*qa, fst sym):(2*qb, snd sym):(List.map (\l -> (l, " | ")) [2*qb+1 .. 2*qa-1])

model (Unary s q) =
  let sym = case List.lookup s unary_gates of
              Just (_, sy) -> sy
              Nothing -> error $ "Undefined unary gate " ++ s
            in
  [(2 * q, sym)]

model (Phase n q) =
  [(2 * q, "[R]")]

model (Controlled g qlist) =
  let pg = model g in
  let (qmin, _) = List.minimum pg
      (qmax, _) = List.maximum pg in
  let (_, _, m) = List.foldl (\(qmn, qmx, mod) q ->
                               if 2*q < qmn then
                                 (2*q, qmx, (2*q, "-*-"):(List.map (\l -> (l, " | ")) [2*q+1 .. qmn-1] ++ mod))
                               else if qmx < 2*q then
                                 (qmn, 2*q, (2*q, "-*-"):(List.map (\l -> (l, " | ")) [qmx+1 .. 2*q-1] ++ mod))
                               else
                                 (qmn, qmx, List.map (\(l, s) -> if l == 2*q then (l, "-*-") else (l, s)) mod)) (qmin, qmax, pg) qlist in
  m

model (Init q bt) =
  [(2 * q, show bt ++ "|-")]

model (Term q bt) =
  [(2 * q, "-|" ++ show bt)]



-- | Definition of a circuit.
data Circuit = Circ {
  qIn :: [Int],     -- ^ List of input wires
  qOut :: [Int],    -- ^ List of output wires
  gates :: [Gate]   -- ^ List of component gates
} deriving Show


-- | A circuit is reversed by reversing the gates and the order of application of the gates.
instance Reversible Circuit where
  rev c =
    Circ {
      qIn = qOut c,
      qOut = qIn c,
      gates = List.map rev $ reverse $ gates c
    }

-- | A circuit is unencaped by unencaping all the gates successively.
instance Caps Circuit where
  unencap c c' b =
    List.foldl (\(nc, b) g -> unencap nc g b) (c, b) (gates c')



--- Circuit pretty printing ---


-- | State that allocates each wire to a line number. When a line
-- becomes unused (after a termination for example), the line is remembered and
-- used to display any new wire.
data Addressing = Address { wires :: Int,         -- ^ Number of wires
                            unused :: [Int],      -- ^ Unused wires
                            bind :: Binding }     -- ^ Binding from addresses to wires

-- | The addressing is hidden in a state monad.
newtype AdState a = AdState (Addressing -> (Addressing, a))
instance Monad AdState where
  return a = AdState (\ad -> (ad, a))
  AdState run >>= action = AdState (\ad -> let (ad', a) = run ad in
                                           let AdState run' = action a in
                                           run' ad')

-- | Returns the addressing state.
get_addressing :: AdState Addressing
get_addressing =
  AdState (\ad -> (ad, ad))


-- | Sets the addressing state.
set_addressing :: Addressing -> AdState ()
set_addressing adr =
  AdState (\_ -> (adr, ()))


-- | Bind the wire to some unused line in the grid.
-- If an existing line is unused, this one is used preferably, else a new line is
-- create.
bind_wire :: Int -> AdState Int
bind_wire q = do
  adr <- get_addressing
  case unused adr of
    [] -> do
        -- No unused line : create a new one
        set_addressing $ adr { wires = (+1) $ wires adr,
                               bind = (q, wires adr):(bind adr) }
        return $ wires adr

    w:cw -> do
        -- Else use the first unused line
        set_addressing $ adr { unused = cw,
                               bind = (q, w):(bind adr) }
        return w


-- | Lookup the number of the line a wire has been associated to.
assoc_wire :: Int -> AdState Int
assoc_wire q = do
  adr <- get_addressing
  case List.lookup q $ bind adr of
    Just w -> return w
    Nothing -> error $ "Circuit construction: Unbound wire " ++ show q


-- | Associated gate : gate whose wires have been replaced by their respective line number.
assoc_gate :: Gate -> AdState Gate
assoc_gate g = do
  binding <- get_addressing >>= return . bind
  return $ readdress g binding


-- | Delete a wire, and set it up to be reused.
delete_vire :: (Int, Int) -> AdState ()
delete_vire (q, w) = do
  adr <- get_addressing
  set_addressing $ adr { unused = w:(unused adr),
                         bind = List.delete (q, w) $ bind adr }


-- | Allocate a list of gates, and returns the list of modified gates.
state_allocate :: [Gate] -> AdState [Gate]
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


-- | Allocate a whole circuit, and returns the modified circuit, along with the total number
-- of used lines.
allocate :: Circuit -> (Circuit, Int)
allocate c =
  let AdState run = do
      -- Bind the input wires (the inputs list is reversed)
      inputs <- List.foldl (\rec w -> do
                              r <- rec
                              w' <- bind_wire w
                              return $ w':r) (return []) $ qIn c
      -- Translate the whole circuit
      gs <- state_allocate $ gates c
      -- Translate the output wires (reversed list)
      outputs <- List.foldl (\rec w -> do
                               r <- rec
                               w' <- assoc_wire w
                               return $ w':r) (return []) $ qOut c
      return $ Circ { qIn = List.reverse inputs,
                      gates = gs,
                      qOut = List.reverse outputs }
      
  in
  -- Run the addressing in the initially empty state
  let (ad, c) = run $ Address { wires = 0, unused = [], bind = [] } in
  (c, wires ad)



-- | If the circuit display can be considered as a grid, this is one of the columns, defined
-- by a map of line numbers to string representation. In reality, each column is three characters wide, and
-- a line can be undefined (it will be interpreted as "   " during the display).
data Column = Col { chars :: Map Int String }


-- | The max number of columns, set to 80 by default (to be divided by the actual width of a column, ie 3).
maxColumns :: Int
maxColumns = 80 


-- | The definition of the whole grid.
data Grid = Grid { gsize :: Int,               -- ^ Number of lines.
                   columns :: [Column],        -- ^ Reversed list of all columns.
                   cut :: Bool }               -- ^ Flag set when the circuit is too long in length.
            
 
-- | Starting from the right of the grid, move left on the line until it finds
-- a column that is not empty. For example, say the line is  [ c b a _ _ _ _ ] where
-- _ indicates that the line is undefined in the current column. The cursor will start
-- at the right, and go left until it finds the character "a", at which point it is blocked.
-- The return value is the column number.
free_depth :: Int -> [Column] -> Int
free_depth l [] = -1
free_depth l (c:cl) = case Map.lookup l $ chars c of
                       Nothing -> 1 + (free_depth l cl)
                       Just _ -> -1

 
-- | Same as free_depth. Instead of moving only on one line, it moves
-- synchronously on a set of lines, and stops as soon as one of the lines is blocked.
free_common_depth :: [Int] -> [Column] -> Int
free_common_depth ls c = List.minimum (List.map (\l -> free_depth l c) ls)


-- | Hide the display grid behind a state monad.
newtype GrState a = GrState (Grid -> (Grid, a))
instance Monad GrState where
  return a = GrState (\gr -> (gr, a))
  GrState run >>= action = GrState (\gr -> let (gr', a) = run gr in
                                           let GrState run' = action a in
                                           run' gr')

-- | Returns the display grid.
get_grid :: GrState Grid
get_grid =
  GrState (\gr -> (gr, gr))


-- | Sets the display grid.
set_grid :: Grid -> GrState ()
set_grid gr =
  GrState (\_ -> (gr, ()))


-- | Prints a 'character' (in fact three) at the coordinates (line, column) in the grid.
print_at :: Int -> Int -> String -> GrState ()
print_at l n s = do
  gr <- get_grid
  at_rec <- return (let at = (\n cols ->
                                case (n, cols) of
                                  (0, c:cs) -> c { chars = Map.insert l s $ chars c }:cs
                                  (n, c:cs) -> c:(at (n-1) cs)) in at)
  cols' <- return $ at_rec n $ columns gr
  set_grid $ gr { columns = cols' }



-- | Prints n characters on same column, different lines.
print_multi :: [(Int, String)] -> GrState ()
print_multi ls = do
  gr <- get_grid
  if not $ cut gr then do
    -- The display stil hasn't overflown
    d <- return $ free_common_depth (fst $ unzip ls) $ columns gr

    if d == -1 then
      -- Free depth = -1 => have to create a new column
      if (List.length $ columns gr) * 6 > maxColumns then
        -- Circuit too long : cut
        set_grid $ gr { cut = True }
      else do
        -- Ok : create the column
        nc <- return $ Col { chars = fromList ls }
        set_grid $ gr { columns = nc:(columns gr) }

    else
      -- Print the characters in column d
      List.foldl (\rec (l, s) -> do
                    rec
                    print_at l d s) (return ()) ls
  else
    return ()


-- | Print a gate.
print_gate :: Gate -> GrState ()
print_gate g = do
  print_multi $ model g


-- | Output the whole line, filling the gaps (undefined lines in column definitions) with space characters.
-- The boolean argument indicates whether the line is of the input wires.
output_line :: Bool -> Int -> GrState String
output_line input l = do
  gr <- get_grid
  -- First characters of the line
  init <- if input then
            return ("---", True)
          else
            return ("   ", False)
  
  -- s is the line being printed, alloc indicates whether the line is currently allocated   
  (s, alloc) <- List.foldr (\c rec -> do
                           (s, alloc) <- rec
                           (s, alloc) <- case Map.lookup l $ chars c of
                                           -- If this column contains an init char on this line, the line is allocated
                                           -- If it is a term char, it is deallocated
                                           -- If it is a vertical wire, and if the line is allocated, fill in the gaps
                                           Just sm -> if isSuffixOf "|-" sm then
                                                        return (s ++ sm, True)
                                                      else if isPrefixOf "-|" sm then
                                                        return (s ++ sm, False)
                                                      else if sm == " | " && alloc then
                                                        return (s ++ "-|-", True)
                                                      else
                                                        return (s ++ sm, alloc)

                                           Nothing -> if alloc then
                                                        return (s ++ "---", alloc)
                                                      else
                                                        return (s ++ "   ", alloc)
      
                           -- Printing wires
                           if alloc then
                             return (s ++ "---", alloc)
                           else
                             return (s ++ "   ", alloc)) (return init) $ columns gr

  -- If the circuit was cut, add some dots..., if not just return the line
  if cut gr && alloc then
    return $ s ++ " .."
  else
    return s


-- | Prints a circuit. It first prints all the gates to the grid, then flushes the grid
-- and returns the resulting string. The integer argument is the total number of allocated lines (supposing it is n,
-- the total number of lines is 2*n -1).
print_circuit :: Circuit -> Int -> String
print_circuit c n =
  let GrState run = do
      -- Print the gates
      List.foldl (\rec g -> do
                    rec
                    print_gate g) (return ()) $ gates c
      -- Output the grid
      gr <- get_grid
      disp <- List.foldl (\rec l -> do
                            s <- rec
                            input <- if l `mod` 2 == 0 then
                                       return $ List.elem (l `quot` 2) $ qIn c
                                     else
                                       return False
                            pl <- output_line input l
                            return $ s ++ pl ++ "\n") (return "") [0 .. gsize gr - 1]
      return disp
  in
  let (_, disp) = run $ Grid { gsize = 2 * n - 1, columns = [], cut = False } in
  "\n" ++ disp ++ "\n"


-- | Pretty printing of a circuit. The function first makes all the necessary bindings
-- wire <-> line, then prints the circuit on a grid, before flushing the whole.
instance PPrint Circuit where
  pprint c =
    let (c', n) = allocate c in
    print_circuit c' n

  sprintn _ c = pprint c
  sprint c = pprint c
  genprint _ c _ = pprint c
