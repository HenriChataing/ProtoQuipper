
module Interpret (-- Only the main function is accessible
                  run) where

import Classes
import Localizing

import Syntax

import Circuits
import Values
import Gates

import Data.Map
import Data.Bool


-- Definition of a new context : empty context with basic gates added
newContext :: Context
---------------------
newContext =
  Ctx { extent = extentUnknown,
        bindings = fromList gateValues,
        circuit = Circ { qIn = [], gates = [], qOut = [] },
        qId = 0 }

-- Extract the bindings from a [let .. = .. in ..] construction, and adds them to the context
bindPattern :: Pattern -> Value -> Context -> Context
------------------------------------------------------
bindPattern (PVar x) v ctx = ctx { bindings = insert x v $ bindings ctx }
bindPattern (PPair p1 p2) (VPair v1 v2) ctx =
  let ctx0 = bindPattern p1 v1 ctx in
  bindPattern p2 v2 ctx0
bindPattern PUnit VUnit ctx = ctx
bindPattern (PLocated p ex) v ctx = bindPattern p v (ctx { extent = ex })
bindPattern _ _ ctx =
  error ("Error : Unmatching pattern, at extent " ++ (show $ extent ctx))

-- Extract the bindings from a circuit application
bind :: Value -> Value -> [(Int, Int)]
--------------------------------------
bind (VQBit q1) (VQBit q2) = [(q1, q2)]
bind (VPair v1 v2) (VPair v1' v2') =
  (bind v1 v1') ++ (bind v2 v2')
bind VUnit VUnit = []
bind v1 v2 =
  error ("Error : Unmatching values : " ++ (show v1) ++ " and " ++ (show v2))

-- Apply a bind function to a value
appBind :: [(Int, Int)] -> Value -> Value
-----------------------------------------
appBind b (VQBit q) = VQBit (applyBinding b q)
appBind b (VPair v1 v2) = VPair (appBind b v1) (appBind b v2)
appBind _ VUnit = VUnit
appBind _ _ =
  error "Error : cannot apply binding function to something not a quantum data"

-- Create a specification (with fresh variables) for a given type
spec :: Type -> Context -> (Value, Context)
-------------------------------------------
spec (TLocated t ex) ctx = spec t (ctx { extent = ex })
spec TQBit ctx = 
  let (q, ctx0) = freshQId ctx in
  (VQBit q, ctx0)
spec (TTensor t1 t2) ctx =
  let (q1, ctx0) = spec t1 ctx in
  let (q2, ctx1) = spec t2 ctx0 in
  (VPair q1 q2, ctx1)
spec TUnit ctx = (VUnit, ctx)
spec t ctx =
  error ("Error : type " ++ (show t) ++ " is not a quantum data type, at extent " ++ (show $ extent ctx))

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
interpretApp :: Value -> Value -> Context -> (Value, Context)

-- Evaluate expressions
interpret :: Expr -> Context -> (Value, Context)

-------------------------

-- Classical beta reduction
interpretApp (VFun c p e) arg ctx =
  let c0 = bindPattern p arg c in
  let c1 = c0 { circuit  = circuit ctx } in
  -- The function body is evaluated in tis own closure, only the circuit differ
  let (v, c2) = interpret e c1 in
  (v, ctx { circuit = circuit c2 })

-- Circuit generation rules
interpretApp VRev (VCirc u c u') ctx = (VCirc u' (rev c) u, ctx)
interpretApp VRev _ ctx = error ("Error : argument expected of type circ, at extent " ++ (show $ extent ctx))

interpretApp (VUnbox (VCirc u c u')) t ctx =
  let b = bind u t in
  let (c0, b0) = unencap (circuit ctx) c b in
  (appBind b0 u', ctx { circuit = c0 })
interpretApp (VUnbox _) _ ctx = error ("Error : Unbox expect a circuit as first argument, at extent " ++ (show $ extent ctx))


-- Location handling
interpret (ELocated e ex) ctx = interpret e (ctx { extent = ex })

-- Empty
interpret EUnit ctx = (VUnit, ctx)

-- Booleans
interpret (EBool b) ctx = (VBool b, ctx)

-- Variables
interpret (EVar x) ctx =
  case Data.Map.lookup x (bindings ctx) of
    Just v -> (v, ctx)
    Nothing -> error ("Error : Unbound variable " ++ x ++ ", at extent " ++ (show $ extent ctx))

-- Functions
  -- The current context is enclosed in the function value
interpret (EFun pl e) ctx = (VFun ctx pl e, ctx)

-- Let .. in ..
  -- first evaluate the expr e1
  -- match it with the pattern
  -- evaluate e2 in the resulting context
interpret (ELet p e1 e2) ctx =
  let (v1, ctx0) = interpret e1 ctx in
  let ctx1 = bindPattern p v1 ctx0 in
  interpret e2 ctx1

-- Function -- englobe all function applications : circuit generating rules and classical reduction
  -- first evaluate the would be function
interpret (EApp ef arg) ctx =
  let (f, ctx0) = interpret ef ctx in
  case f of
    -- Classical beta reduction
    VFun _ _ _ ->
        let (t, ctx1) = interpret arg ctx0 in
        interpretApp f t ctx1 
    -- Circuit unboxing
    VUnbox _ ->
        let (t, ctx1) = interpret arg ctx0 in
        interpretApp f t ctx1
    -- Circuit reversal
    VRev ->
        let (t, ctx1) = interpret arg ctx0 in
        interpretApp f t ctx1

    -- Circuit boxing
    VBox typ ->
        -- Creation of a new specification
        let (s, ctx1) = spec typ ctx0 in  
        let qd = extract s in
        -- Open a new context
        let nctx = ctx1 { circuit = Circ { qIn = qd, gates = [], qOut = qd } }  in
        -- Execute the argument, applied to the specification, in the new context
        let (m, nctx0) = interpret arg nctx in
        let (s', nctx1) = interpretApp m s nctx0 in
        (VCirc s (circuit nctx1) s', ctx1)
    _ -> error ("Error : value is not a function, at extent " ++ (show $ extent ctx0))

-- Pairs
interpret (EPair e1 e2) ctx =
  let (v1, ctx0) = interpret e1 ctx in
  let (v2, ctx1) = interpret e2 ctx0 in
  (VPair v1 v2, ctx1)

-- If .. then .. else ..
interpret (EIf e1 e2 e3) ctx =
  let (v1, ctx0) = interpret e1 ctx in
  case v1 of
    VBool True -> interpret e2 ctx0
    VBool False -> interpret e3 ctx0
    _ -> error ("Error : Condition is not a boolean, at extent " ++ (show $ extent ctx))

-- Some congruence rules
interpret (EBox t) ctx = (VBox t, ctx)
interpret ERev ctx = (VRev, ctx)
interpret (EUnbox e) ctx =
  let (v, ctx0) = interpret e ctx in
  (VUnbox v, ctx0)

-------------------
-- Main function --

run :: Expr -> Value
--------------------
run e =
  let (v, _) = interpret e newContext in
  v
