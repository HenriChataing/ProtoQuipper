
module Interpret (-- Only the main function is accessible
                  run) where

import Classes
import Localizing
import qualified Utils

import Syntax
import Printer

import Values
import Gates

-- Import the basic gates in the current context
importGates :: State ()
---------------------
importGates = State (\c ->
                       foldl (\(c', _) (gate, circ) -> let State run = insert gate circ in
                                                       run c') (c, Utils.Ok ()) gate_values)

-- Extract the bindings from a [let .. = .. in ..] construction, and adds them to the context
bind_pattern :: Pattern -> Value -> State ()
------------------------------------------------------
bind_pattern (PVar x) v = do
  insert x v
bind_pattern (PPair p1 p2) (VPair v1 v2) = do
  bind_pattern p1 v1
  bind_pattern p2 v2
bind_pattern PUnit VUnit = do
  return ()
bind_pattern (PLocated p ex) v = do
  set_extent ex
  bind_pattern p v
bind_pattern p q = do
  fail ("Unmatching patterns : " ++ sprint p ++ " and " ++ sprint q)

-- Extract the bindings from a circuit application
bind :: Value -> Value -> State [(Int, Int)]
--------------------------------------
bind (VQBit q1) (VQBit q2) = do
  return [(q1, q2)]
bind (VPair v1 v2) (VPair v1' v2') = do
  b1 <- bind v1 v1'
  b2 <- bind v2 v2'
  return (b1 ++ b2)
bind VUnit VUnit = do
  return []
bind v1 v2 = do
  fail ("Unmatching values : " ++ pprint v1 ++ " and " ++ pprint v2)

-- Apply a bind function to a value
apply_binding :: [(Int, Int)] -> Value -> State Value
-----------------------------------------
apply_binding b (VQBit q) = do 
  return (VQBit $ Utils.apply_binding b q)
apply_binding b (VPair v1 v2) = do
  v1' <- apply_binding b v1
  v2' <- apply_binding b v2
  return (VPair v1' v2')
apply_binding _ VUnit = do
  return VUnit
apply_binding _ v = do
  fail ("Expected a quantum data value - Actual value : " ++ pprint v)

-- Create a specification (with fresh variables) for a given type
spec :: Type -> State Value
-------------------------------------------
spec (TLocated t ex) = do
  set_extent ex
  spec t
spec TQBit = do
  q <- new_id
  return (VQBit q)
spec (TTensor t1 t2) = do
  q1 <- spec t1
  q2 <- spec t2
  return (VPair q1 q2)
spec TUnit = do
  return VUnit
spec t = do
  fail ("Expected a quantum data type - Actual type : " ++ pprint t)

-- Extract the quantum addresses used in a value
extract :: Value -> State [Int]
-------------------------
extract (VQBit q) = do
  return [q]
extract (VPair v1 v2) = do
  q1 <- extract v1
  q2 <- extract v2
  return (q1 ++ q2)
extract VUnit = do
  return []
extract v = do
  fail ("Expected a quantum data value - Actual value : " ++ pprint v)

-------------------------
----- Interpreter -------

-- Evaluate function application
interpret_app :: Value -> Value -> State Value

-- Evaluate expressions
interpret :: Expr -> State Value

-------------------------

-- Classical beta reduction
interpret_app (VFun c p e) arg = do
  ctx <- swap_context c  -- See module Values : ctx is the old context, the circuit is left unchanged
  bind_pattern p arg
  v <- interpret e
  _ <- swap_context ctx
  return v

-- Circuit generation rules
interpret_app VRev (VCirc u c u') = do
  return (VCirc u' (rev c) u)

interpret_app VRev e  = do
  fail ("Expected argument of type circ - Actual expression : " ++ sprint e)

interpret_app (VUnbox (VCirc u c u')) t = do
  b <- bind u t
  b' <- unencap c b
  apply_binding b' u'

interpret_app (VUnbox e) _  = do
  fail ("Expected argument of type circ - Actual expression : " ++ sprint e)

-- Pattern matching with the list of cases
interpret_match (VInjL v) ((p, f):pc) = do
  bind_pattern p v
  interpret f

interpret_match (VInjR v) [_, (p, f)] = do
  bind_pattern p v
  interpret f

interpret_match (VInjR v) (_:pc) = do
  interpret_match v pc

-- Location handling
interpret (ELocated e ex) = do
  set_extent ex
  interpret e

-- Empty
interpret EUnit = do
  return VUnit

-- Booleans
interpret (EBool b) = do
  return (VBool b)

-- Variables
interpret (EVar x) = do
  find x

-- Functions
  -- The current context is enclosed in the function value
interpret (EFun p e) = do
  ctx <- get_context
  return (VFun ctx p e)

-- Let .. in ..
  -- first evaluate the expr e1
  -- match it with the pattern
  -- evaluate e2 in the resulting context
    -- The state at the end must contains only the bindings from the state at the beginning
interpret (ELet p e1 e2) = do
  ctx <- get_context
  v1 <- interpret e1
  bind_pattern p v1
  v2 <- interpret e2
  put_context ctx -- Erase the bindings introduced by the let construction
  return v2

-- Function -- englobe all function applications : circuit generating rules and classical reduction
  -- first evaluate the would be function
interpret (EApp ef arg) = do
  f <- interpret ef
  case f of
    -- Classical beta reduction
    VFun _ _ _ -> do
        t <- interpret arg
        interpret_app f t
    -- Circuit unboxing
    VUnbox _ -> do
        t <- interpret arg
        interpret_app f t
    -- Circuit reversal
    VRev -> do
        t <- interpret arg
        interpret_app f t

    -- Circuit boxing
    VBox typ -> do
        -- Creation of a new specification
        s <- spec typ
        -- Open a new circuit
        ql <- extract s
        c <- open_box ql
        -- Execute the argument, applied to the specification, in the new context
        m <- interpret arg
        s' <- interpret_app m s
        -- Close the new circuit and reset the old one
        c' <- close_box c
        return (VCirc s c' s')

    _ -> do
        fail ("Expected value of type function - Actual expression : " ++ sprint ef)

-- Patterns and pattern matching
interpret (EInjL e) = do
  v <- interpret e
  return (VInjL v)

interpret (EInjR e) = do
  v <- interpret e
  return (VInjR v)

interpret (EMatch e plist) = do
  v <- interpret e
  ctx <- get_context
  v' <- interpret_match v plist
  put_context ctx
  return v'

-- Pairs
interpret (EPair e1 e2) = do
  v1 <- interpret e1
  v2 <- interpret e2
  return (VPair v1 v2)

-- If .. then .. else ..
interpret (EIf e1 e2 e3) = do
  v1 <- interpret e1
  case v1 of
    VBool True -> do
        interpret e2
    VBool False -> do
        interpret e3
    _ -> do
        fail ("Expected value of type bool - Actual expression : " ++ sprint e1)

-- Some congruence rules
interpret (EBox t) = do
  return (VBox t)
interpret ERev = do
  return VRev
interpret (EUnbox e) = do
  v <- interpret e
  return (VUnbox v)

-------------------
-- Main function --

run :: Expr -> Utils.Computed Value
--------------------
run e =
  let State runstate = do
                         importGates
                         interpret e
                       in
  let (_, v) = runstate empty_context in
  v
