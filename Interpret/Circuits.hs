-- | This module is all about working with circuits. It includes definitions of the basic
-- circuit gates, the data type definition of a circuit, along with all the semantic
-- operations such as encapsulating, printing, etc.
-- In summary:
--
-- * Gates are classified by category: init and term gates together, phase gates (parameterized over the angle), and unary and the binary gates
--   together. Controlled gates are not supported by the syntax yet, but still a dedicated constructor is present.
--
-- * Circuits are represented by: lists of input and output wires, and a list of gates.
--
module Interpret.Circuits where

import Data.List as List
import Data.Map as Map

import Classes


-- | The list of unary gates.
-- Unary gates are defined by: their name, the name of the reversed gate, and the symbol used to represent it in
-- the display of the circuit (three characters).
unary_gates :: [(String, (String, String))]
unary_gates =
  [ ("GATE_H", ("GATE_H", "-H-")),
    ("NOT", ("NOT", "(+)")),
    ("GATE_X", ("GATE_X", "-X-")),
    ("GATE_Y", ("GATE_Y", "-Y-")),
    ("GATE_Z", ("GATE_Z", "-Z-")),
    ("GATE_S", ("GATE_S_INV", "-S-")),
    ("GATE_S_INV", ("GATE_S", "-S*")),
    ("GATE_T", ("GATE_T_INV", "-T-")),
    ("GATE_T_INV", ("GATE_T", "-T*")),
    ("GATE_E", ("GATE_E_INV", "-E-")),
    ("GATE_E_INV", ("GATE_E", "-E*")),
    ("GATE_OMEGA", ("GATE_OMEGA", "-W-")),
    ("GATE_V", ("GATE_V_INV", "-V-")),
    ("GATE_V_INV", ("GATE_V", "-V*")), 
    ("GATE_EITZ", ("GATE_EITZ_INV", "-R-")),
    ("GATE_EITZ_INV", ("GATE_EITZ", "-R*"))
    ]


-- | The list of binary gates.
-- The definition of a binary gate is similar to that of a unary one, except for the symbolic
-- representation, which now takes two characters, one for each wire.
binary_gates :: [(String, (String, (String, String)))]
binary_gates =
  [ ("SWAP", ("SWAP", ("-x-", "-x-"))),
    ("CNOT", ("CNOT", ("(+)", "-*-"))),
    ("GATE_W", ("GATE_W", ("-W1", "-W2"))) ]



-- | A type class for objects that can be unencapsulated. Typical examples are
-- gates and circuits.
class Caps a where
  -- | Unencapsulate a circuit (or gate circuit). The type follows the operational semantics of Proto-Quipper.
  unencap :: Circuit               -- ^ The base circuit.
          -> a                     -- ^ The circuit (gate circuit) that is to be appended.
          -> Binding               -- ^ A binding function.
          -> (Circuit, Binding)    -- ^ Returns the resulting circuit, together with a mapping from the output wires
                                   -- of the appended circuit to new wire identifiers.


-- | A binding is defined as a list of mappings q |-> q'.
type Binding = [(Int, Int)]


-- | Apply a binding. The binding function behaves as the identity function
-- on addresses that are not in the mapping list.
apply_binding :: [(Int, Int)] -> Int -> Int
apply_binding b a =
  case List.lookup a b of
  Just a' -> a'
  Nothing -> a


-- | Given the input of a circuit, select an new unused address.
-- Since no list keeps track of the unused wires, new wire identifiers are chosen by taking the smallest value
-- not yet in use.
fresh_address :: [Int] -> Int
fresh_address [] = 0
fresh_address l = (maximum l) + 1


-- | Definition of the basic gates.
data Gate =
    Init Int Int            -- ^ The initialization gates  @0|-@  and  @1|-@.
  | Term Int Int            -- ^ The assertive termination gates  @-|0@  and  @-|1@.
  | Phase Int Int           -- ^ The phase gate, represented by the matrix:
                            -- 
                            -- @
                            --               | 1        0     |
                            --        R(n) = |                |
                            --               | 0   e^(i Pi/n) |
                            -- @
  | Unary String Int        -- ^ Unary gates. The first argument is the gate name, which must belong to the list 'unary_gates' defined above.
  | Binary String Int Int   -- ^ Binary gates. The first argument is the gate name, which must belong to the list 'binary_gates'.
  | Controlled Gate [Int]   -- ^ Controlled gates. The second argument is a list of control wires, not necessarily linear.
                            -- This constructor will have to be elaborated as soon as controls are added to Proto-Quipper syntax to
                            -- be able to distinguish between positive and negative controls.
    deriving Show


-- | Re-address a gate by applying the given binding to its inputs and outputs.
readdress :: Gate -> Binding -> Gate
readdress (Phase n q) b = Phase n (apply_binding b q)
readdress (Unary s q) b = Unary s (apply_binding b q)
readdress (Binary s qa qb) b = Binary s (apply_binding b qa) (apply_binding b qb)
readdress (Controlled g qlist) b = Controlled (readdress g b) (List.map (apply_binding b) qlist)


-- | The reverse function on gates uses the definition of the unary / binary gates
-- to know the name of the reversed gate.
instance Reversible Gate where
  -- Init and term are mutual inverses
  rev (Init b q) = Term b q
  rev (Term b q) = Init b q

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


-- | Gates can be unencapsulated. The wires of the gate are renamed to match the wires to which the gate is
-- to be appended, and then the gate is added to the list of gates of the circuit.
-- The input and output wires of the circuit may be modified by appending /init/ or /term/ gates. 
instance Caps Gate where
  -- Normal gates
  unencap c g@(Phase _ _) b = (c { gates = (gates c) ++ [readdress g b] }, b)
  unencap c g@(Unary _ _) b = (c { gates = (gates c) ++ [readdress g b] }, b)
  unencap c g@(Binary _ _ _) b = (c { gates = (gates c) ++ [readdress g b] }, b)
  unencap c (Controlled g qlist) b = (c { gates = (gates c) ++ [readdress (Controlled g qlist) b] }, b)

  -- Creation / deletion of wires
  unencap c (Term bt q) b = let q' = apply_binding b q in
    (c { gates = (gates c) ++ [Term bt q'], qOut = List.delete q' (qOut c) }, List.delete (q, q') b)
  unencap c (Init bt q) b = let q' = fresh_address (qOut c) in
    (c { gates = (gates c) ++ [Init bt q'], qOut = q':(qOut c) }, (q, q'):b)


-- | Return the gate concrete display. More specifically, each gate is printed in one column, and this function
-- returns what part of a gate appears on what line. For example, considering the gate CNOT (0, 1), its display is
--
-- @
--  0  (+)
--  1   |
--  2  -*-
-- @
-- 
-- and the return value is
-- 
-- @
--   (0, \"(+)\"), (1, \" | \"), (2, \"-*-\")
-- @
-- 
-- Note that the wire identifiers are multiplied by two, as intermediate lines are added to lighten the display.
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
  [(2 * q, "-R-")]

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

model (Init bt q) =
  [(2 * q, show bt ++ "|-")]

model (Term bt q) =
  [(2 * q, "-|" ++ show bt)]



-- | The data type of circuits.
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

-- | A circuit is unencapsulated by unencapsulating all the gates successively.
instance Caps Circuit where
  unencap c c' b =
    List.foldl (\(nc, b) g -> unencap nc g b) (c, b) (gates c')



--- Circuit pretty printing ---


-- | This data type defines a state that allocates each wire to a line
-- number. When a line becomes unused (after a termination, for
-- example), the line is remembered and used to display any new wire.
data Addressing = Address { wires :: Int,         -- ^ Number of wires.
                            unused :: [Int],      -- ^ Unused wires.
                            bind :: Binding }     -- ^ Binding from addresses to wires.

-- | A state monad to hide the addressing.
newtype AdState a = AdState (Addressing -> (Addressing, a))
instance Monad AdState where
  return a = AdState (\ad -> (ad, a))
  AdState run >>= action = AdState (\ad -> let (ad', a) = run ad in
                                           let AdState run' = action a in
                                           run' ad')

-- | Return the addressing state.
get_addressing :: AdState Addressing
get_addressing =
  AdState (\ad -> (ad, ad))


-- | Set the addressing state.
set_addressing :: Addressing -> AdState ()
set_addressing adr =
  AdState (\_ -> (adr, ()))


-- | Bind a wire to some unused line in the grid.  If an existing line
-- is unused, it is used preferentially; otherwise a new line is
-- created.
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


-- | Look up the line number a wire has been mapped to.
assoc_wire :: Int -> AdState Int
assoc_wire q = do
  adr <- get_addressing
  case List.lookup q $ bind adr of
    Just w -> return w
    Nothing -> error $ "Circuit construction: Unbound wire " ++ show q


-- | Return the associated gate: a gate whose wires have been replaced by their respective line numbers.
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


-- | Allocate a list of gates, and return the list of modified gates.
state_allocate :: [Gate] -> AdState [Gate]
state_allocate [] = do
  return []

state_allocate (Init bt q:cg) = do
  w <- bind_wire q
  cg' <- state_allocate cg
  return (Init bt w:cg')

state_allocate (Term bt q: cg) = do
  w <- assoc_wire q
  delete_vire (q, w)
  cg' <- state_allocate cg
  return (Term bt w:cg')

state_allocate (g:cg) = do
  g' <- assoc_gate g
  cg' <- state_allocate cg
  return (g':cg')


-- | Allocate a whole circuit, and return the modified circuit, along with the total number
-- of lines that are occupied.
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



-- | A data type to encode a column of the circuit visual display. It is represented by a map
-- associating each line to its content. The map need not be complete, and missing lines
-- will be considered as empty spaces.
data Column = Col {
  chars :: Map Int String  -- ^ Line by line representation of the column.
}


-- | The maximum number of characters that can fit the console screen.
-- By default, it is set to 80 (to be divided by the actual width of a column, i.e., 3). It would be possible to use
-- the library "System.Console.ANSI" to get the actual width of the screen; however, this would mean another library to install.
maxColumns :: Int
maxColumns = 80 


-- | A type to hold the whole grid on which a circuit is drawn.
data Grid = Grid { gsize :: Int,               -- ^ Number of lines.
                   columns :: [Column],        -- ^ Reversed list of all columns.
                   cut :: Bool }               -- ^ Flag set when the circuit is too long in length.


-- | Starting from the right of the grid, move left on the line until a non-empty column is found.
-- For example, say the line is  [ c b a _ _ _ _ ] where
-- _ indicates that the line is undefined in the current column. The cursor will start
-- at the right, and go left until it finds the character "a", at which point it is blocked.
-- The return value is this specific column's number.
free_depth :: Int -> [Column] -> Int
free_depth l [] = -1
free_depth l (c:cl) = case Map.lookup l $ chars c of
                       Nothing -> 1 + (free_depth l cl)
                       Just _ -> -1

 
-- | Like 'free_depth', but instead of moving only on one line, move
-- synchronously on a set of lines, and stop as soon as one of the lines is blocked.
free_common_depth :: [Int] -> [Column] -> Int
free_common_depth ls c = List.minimum (List.map (\l -> free_depth l c) ls)


-- | A state monad to hide the display grid.
newtype GrState a = GrState (Grid -> (Grid, a))
instance Monad GrState where
  return a = GrState (\gr -> (gr, a))
  GrState run >>= action = GrState (\gr -> let (gr', a) = run gr in
                                           let GrState run' = action a in
                                           run' gr')

-- | Return the current display grid.
get_grid :: GrState Grid
get_grid =
  GrState (\gr -> (gr, gr))


-- | Set the current display grid.
set_grid :: Grid -> GrState ()
set_grid gr =
  GrState (\_ -> (gr, ()))


-- | Print a \"character\" (in fact, three) at the coordinates (/line/, /column/) in the grid.
print_at :: Int -> Int -> String -> GrState ()
print_at l n s = do
  gr <- get_grid
  at_rec <- return (let at = (\n cols ->
                                case (n, cols) of
                                  (0, c:cs) -> c { chars = Map.insert l s $ chars c }:cs
                                  (n, c:cs) -> c:(at (n-1) cs)) in at)
  cols' <- return $ at_rec n $ columns gr
  set_grid $ gr { columns = cols' }



-- | Print /n/ characters on different lines of the same column.
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
output_line :: Bool             -- ^ Indicates whether the line is one of the input wires (which means it has to be printed).
            -> Int              -- ^ The line number.
            -> GrState String   -- ^ The complete line.
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


-- | Print a circuit. This first prints all the gates to the grid, then flushes the grid
-- and returns the resulting string. The integer argument is the total number of allocated lines (if it is /n/,
-- the total number of lines is 2*/n/-1).
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
  let (_, disp) = run $ Grid { gsize = 2 * n - 1, columns = [], cut = False } in
  "\n" ++ disp ++ "\n"


-- | Pretty printing of a circuit. The function first makes all the necessary bindings
-- wire \<-\> line, then prints the circuit on a grid, before flushing the whole output.
instance PPrint Circuit where
  pprint c =
    let (c', n) = allocate c in
    print_circuit c' n

  sprintn _ c = pprint c
  sprint c = pprint c
  genprint _ c _ = pprint c
