
module Interpret where

import Syntax
import Circ
import Localizing

import Data.Map
import Data.Bool

data Value =
    VFun Context Pattern Expr
  | VPair Value Value
  | VCirc Value Circuit Value
  | VBool Bool
  | VBox Type
  | VUnbox Value
  | VEmpty
  | VRev
  | VQBit Int     -- Quantum addresses

data Context =
  Ctx {
    -- Localization (extent of the current expression/type/pattern
    extent :: Extent,

    -- Variable bindings
    bindings :: Map String Value,

    -- Current circuit
    circuit :: Circuit,

    -- For quantum id generation
    freeQid :: [Int],
    qid :: Int
  }

basicGates :: [(String, Value)]
basicGates =
  [ ("H",    VCirc (VQBit 0) (Circ { qIn = [0], gates = [ Hadamard 0 ], qOut = [0] }) (VQBit 0)),
    ("CNOT", VCirc (VPair (VQBit 0) (VQBit 1)) (Circ { qIn = [0, 1], gates = [ CNot 0 1 ], qOut = [0, 1] }) (VPair (VQBit 0) (VQBit 1))),
    ("NOT",  VCirc (VQBit 0) (Circ { qIn = [0], gates = [ Not 0 ], qOut = [0] }) (VQBit 0)) ]

newContext :: Context
newContext =
  Ctx {
    extent = extentUnknown,
    bindings = fromList basicGates,

    circuit = Circ { qIn = [], qOut = [], gates = [] },

    freeQid = [],
    qid = 0
  }

-- Generate a fresh qbit id
freshQId :: Context -> (Int, Context)
freshQId ctx =
  case freeQid ctx of
    [] -> (qid ctx, ctx { qid = (+1) $ qid ctx })
    id:r -> (id, ctx { freeQid = r })

-- Extract the bindings from a [let .. = .. in ..] construction, and adds them to the context
matchPattern :: Pattern -> Value -> Context -> Context
matchPattern (PVar x) v ctx = ctx { bindings = insert x v $ bindings ctx }
matchPattern (PPair p1 p2) (VPair v1 v2) ctx =
  let ctx = matchPattern p1 v1 ctx in
  matchPattern p2 v2 ctx
matchPattern (PLocated p ex) v ctx = matchPattern p v (ctx { extent = ex }) 
matchPattern _ _ ctx =
  error ("Error : Unmatching pattern, at extent " ++ (show $ extent ctx))

-- Extract the bindings from a circuit application
bind :: Value -> Value -> [(Int, Int)]
bind (VQBit q1) (VQBit q2) = [(q1, q2)]
bind (VPair v1 v2) (VPair v1' v2') =
  (bind v1 v1') ++ (bind v2 v2')
bind _ _ =
  error "Error : Unmatching value"

-- Apply the bind function to the value
revBind :: [(Int, Int)] -> Value -> Value
revBind b (VQBit q) = VQBit (applyBinding b q)
revBind b (VPair v1 v2) = VPair (revBind b v1) (revBind b v2)
revBind _ _ =
  error "Error : cannot apply binding function to something not a quantum data"

-- Create a specification (with fresh variables) for a given type
spec :: Type -> Context -> (Value, Context)
spec (TLocated t ex) ctx = spec t (ctx { extent = ex })
spec TQBit ctx = 
  let (q, ctx) = freshQId ctx in
  (VQBit q, ctx)
spec (TTensor t1 t2) ctx =
  let (q1, ctx) = spec t1 ctx in
  let (q2, ctx) = spec t2 ctx in
  (VPair q1 q2, ctx)
spec t ctx =
  error ("Error : type " ++ (show t) ++ " is not a quantum data type, at extent " ++ (show $ extent ctx))

-- Extract the quantum addresses used in a value
extract :: Value -> [Int]
extract (VQBit q) = [q]
extract (VPair v1 v2) = (extract v1) ++ (extract v2)
extract _ = error "Error : cannot extract the quantum addresses of something not a quantum data"

-----------------------
----- Interpret -------

interpret :: Expr -> Context -> (Value, Context)

-- Location handling
interpret (ELocated e ex) ctx = interpret e (ctx { extent = ex })

-- Empty
interpret EEmpty ctx = (VEmpty, ctx)

-- Booleans
interpret (EBool b) ctx = (VBool b, ctx)

-- Variables
interpret (EVar x) ctx =
  case Data.Map.lookup x (bindings ctx) of
    Just v -> (v, ctx)
    Nothing -> error ("Error : Unbound variable " ++ x ++ ", at extent " ++ (show $ extent ctx))

-- Functions
interpret (EFun pl e) ctx = (VFun ctx pl e, ctx)

-- Let .. in ..
interpret (ELet p e1 e2) ctx =
  let (v1, ctx) = interpret e1 ctx in
  let ctx = matchPattern p v1 ctx in
  interpret e2 ctx

-- Intercept unbox
interpret (EApp EUnbox e) ctx =
  let (c, ctx) = interpret e ctx in
  (VUnbox c, ctx)

-- Function
interpret (EApp e1 e2) ctx =
  case interpret e1 ctx of
    (VFun c p e, ctx) ->
        let (v, ctx) = interpret e2 ctx in
        let c = matchPattern p v c in
        let (v, _) = interpret e c in
        (v, ctx)
    (VUnbox (VCirc u c u'), ctx) ->
        let (t, ctx) = interpret e2 ctx in
        let b = bind u t in
        let (c', b') = unencap b (circuit ctx) c' in
        (revBind b' u', ctx { circuit = c' })
    (VRev, ctx) ->
        let (v, ctx) = interpret e2 ctx in
        case v of
          VCirc u c u' ->
              (VCirc u' (rev c) u, ctx)
          _ ->
              error ("Error : cannot reverse something not a circuit, at extent " ++ (show $ extent ctx))
    (VBox t, ctx) ->
        let (s, ctx) = spec t ctx in
        let qd = extract s in
        let nctx = ctx { circuit = Circ { qIn = qd, gates = [], qOut = qd } }  in
        let (s', nctx) = interpret e2 nctx in
        (VCirc s (circuit nctx) s', ctx)
    _ -> error "Not supported yet : circuit generating rules"

-- Pairs
interpret (EPair e1 e2) ctx =
  let (v1, ctx) = interpret e1 ctx in
  let (v2, ctx) = interpret e2 ctx in
  (VPair v1 v2, ctx)

-- If .. then .. else ..
interpret (EIf e1 e2 e3) ctx =
  case interpret e1 ctx of
    (VBool True, ctx) -> interpret e2 ctx
    (VBool False, ctx) -> interpret e3 ctx
    _ -> error ("Condition is not a boolean at extent " ++ (show $ extent ctx))

-- Ciruit generation rules
interpret (EBox t) ctx = (VBox t, ctx)
interpret ERev ctx = (VRev, ctx)


