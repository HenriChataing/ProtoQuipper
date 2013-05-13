
module Interpret (-- Only the main function is accessible
                  run) where

import Classes
import Localizing
import qualified Utils as Binding

import Syntax

import Values
import Gates


-- Import the basic gates in the current context
importGates :: State ()
---------------------
importGates = State (\c ->
                       foldl (\(c', _) (gate, circ) -> let State run = insert gate circ in
                                                       run c') (c, ()) Gates.gateValues)

-- Extract the bindings from a [let .. = .. in ..] construction, and adds them to the context
bindPattern :: Pattern -> Value -> State ()
------------------------------------------------------
bindPattern (PVar x) v = do
  insert x v
bindPattern (PPair p1 p2) (VPair v1 v2) = do
  bindPattern p1 v1
  bindPattern p2 v2
bindPattern PUnit VUnit = do
  return ()
bindPattern (PLocated p ex) v = do
  setExtent ex
  bindPattern p v
bindPattern _ _ = do
  ext <- getExtent
  error ("Error : Unmatching pattern, at extent " ++ show ext)

-- Extract the bindings from a circuit application
bind :: Value -> Value -> [(Int, Int)]
--------------------------------------
bind (VQBit q1) (VQBit q2) = [(q1, q2)]
bind (VPair v1 v2) (VPair v1' v2') =
  (bind v1 v1') ++ (bind v2 v2')
bind VUnit VUnit = []
bind v1 v2 =
  error ("Error : Unmatching values : " ++ show v1 ++ " and " ++ show v2)

-- Apply a bind function to a value
appBind :: [(Int, Int)] -> Value -> Value
-----------------------------------------
appBind b (VQBit q) = VQBit (Binding.apply b q)
appBind b (VPair v1 v2) = VPair (appBind b v1) (appBind b v2)
appBind _ VUnit = VUnit
appBind _ _ =
  error "Error : cannot apply binding function to something not a quantum data"

-- Create a specification (with fresh variables) for a given type
spec :: Type -> State Value
-------------------------------------------
spec (TLocated t ex) = do
  setExtent ex
  spec t
spec TQBit = do
  q <- newId
  return (VQBit q)
spec (TTensor t1 t2) = do
  q1 <- spec t1
  q2 <- spec t2
  return (VPair q1 q2)
spec TUnit = do
  return VUnit
spec t = do
  ext <- getExtent
  error ("Error : type " ++ show t ++ " is not a quantum data type, at extent " ++ show ext)

-- Extract the quantum addresses used in a value
extract :: Value -> [Int]
-------------------------
extract (VQBit q) = [q]
extract (VPair v1 v2) = (extract v1) ++ (extract v2)
extract VUnit = []
extract _ = error "Error : cannot extract the quantum addresses of something not a quantum data"

-------------------------
----- Interpreter -------

-- Evaluate function application
interpretApp :: Value -> Value -> State Value

-- Evaluate expressions
interpret :: Expr -> State Value

-------------------------

-- Classical beta reduction
interpretApp (VFun c p e) arg = do
  ctx <- swapContext c  -- See module Values : ctx is the old context, the circuit is left unchanged
  bindPattern p arg
  v <- interpret e
  _ <- swapContext ctx
  return v

-- Circuit generation rules
interpretApp VRev (VCirc u c u') = do
  return (VCirc u' (rev c) u)

interpretApp VRev _  = do
  ext <- getExtent
  error ("Error : argument expected of type circ, at extent " ++ show ext)

interpretApp (VUnbox (VCirc u c u')) t = do
  b' <- unencap c (bind u t)
  return (appBind b' u')

interpretApp (VUnbox _) _  = do
  ext <- getExtent
  error ("Error : Unbox expect a circuit as first argument, at extent " ++ show ext)


-- Location handling
interpret (ELocated e ex) = do
  setExtent ex
  interpret e

-- Empty
interpret EUnit = do
  return VUnit

-- Booleans
interpret (EBool b) = do
  return (VBool b)

-- Variables
interpret (EVar x) = do
  v <- find x
  case v of
    Just v -> do
        return v
    Nothing -> do
        ext <- getExtent
        error ("Error : Unbound variable " ++ x ++ ", at extent " ++ show ext)

-- Functions
  -- The current context is enclosed in the function value
interpret (EFun p e) = do
  ctx <- getContext
  return (VFun ctx p e)

-- Let .. in ..
  -- first evaluate the expr e1
  -- match it with the pattern
  -- evaluate e2 in the resulting context
    -- The state at the end must contains only the bindings from the state at the beginning
interpret (ELet p e1 e2) = do
  ctx <- getContext
  v1 <- interpret e1
  bindPattern p v1
  v2 <- interpret e2
  putContext ctx -- Erase the bindings introduced by the let construction
  return v2

-- Function -- englobe all function applications : circuit generating rules and classical reduction
  -- first evaluate the would be function
interpret (EApp ef arg) = do
  f <- interpret ef
  case f of
    -- Classical beta reduction
    VFun _ _ _ -> do
        t <- interpret arg
        interpretApp f t
    -- Circuit unboxing
    VUnbox _ -> do
        t <- interpret arg
        interpretApp f t
    -- Circuit reversal
    VRev -> do
        t <- interpret arg
        interpretApp f t

    -- Circuit boxing
    VBox typ -> do
        -- Creation of a new specification
        s <- spec typ
        -- Open a new circuit
        c <- openBox (extract s)
        -- Execute the argument, applied to the specification, in the new context
        m <- interpret arg
        s' <- interpretApp m s
        -- Close the new circuit and reset the old one
        c' <- closeBox c
        return (VCirc s c' s')

    _ -> do
        ext <- getExtent
        error ("Error : value is not a function, at extent " ++ show ext)

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
        ext <- getExtent
        error ("Error : Condition is not a boolean, at extent " ++ show ext)

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

run :: Expr -> Value
--------------------
run e =
  let State runstate = do
                         importGates
                         interpret e
                       in
  let (_, v) = runstate emptyContext in
  v
