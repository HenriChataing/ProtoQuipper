module TypeInference where

import Syntax
import Localizing

import Data.Map
import Data.List

-- Infinite set of type variables --
ints = iterate (+1) 0
varSet = Data.List.map (\n -> "?X" ++ (show n)) ints

-- Extract the int id of such generated names
extractId :: String -> Int
--------------------------
extractId s = (read $ tail $ tail s) :: Int

------------------------------------

-- Context : each variable is associated with a typing scheme
data Context =
  Ctx {
    -- Location information
    extent :: Extent,

    -- Typing information
    bindings :: Map String Scheme,

    -- Type constraints
    constraints :: [(Type, Type)],

    -- Set of unused variables
    vars :: [String]
  }

-- Generate a fresh name
freshName :: Context -> (String, Context)
-----------------------------------------
freshName ctx = (head $ vars ctx, ctx { vars = tail $ vars ctx })

-- Generate a fresh type variable, and binds it with the variable
bindVariable :: String -> Context -> (Type, Context)
----------------------------------------------------
bindVariable x ctx =
  let t = TVar (head $ vars ctx) in
  (t, ctx { bindings = Data.Map.insert x ([], t) $ bindings ctx, vars = tail $ vars ctx })

-- Generate fresh variables enough for a pattern
bindPattern :: Pattern -> Context -> (Type, Context)
----------------------------------------------------------------
bindPattern (PLocated p ex) ctx = bindPattern p (ctx { extent = ex }) 
bindPattern PUnit ctx = (TUnit, ctx)
bindPattern (PVar x) ctx = bindVariable x ctx
bindPattern (PPair p1 p2) ctx =
  let (t1, ctx1) = bindPattern p1 ctx in
  let (t2, ctx2) = bindPattern p2 ctx1 in
  (TTensor t1 t2, ctx2)
-- A constraint is generated binding the inferred type to the given one
bindPattern (PConstraint p typ) ctx =
  let (t, ctx0) = bindPattern p ctx in
  (t, ctx0 { constraints = (t, typ):(constraints ctx0) })

-- Match a pattern with a type and generate the appropriate constraints
matchPattern :: Pattern -> Type -> Context -> ([(String, Type)], Context)
-------------------------------------------------------------------------
matchPattern (PLocated p _) t ctx = matchPattern p t ctx
matchPattern PUnit t ctx = ([], ctx { constraints = (t, TUnit):(constraints ctx) })
matchPattern (PVar x) t ctx = ([(x, t)], ctx)
-- Since this function is called in let bindings, pattern constraints have yet to be registered
matchPattern (PConstraint p typ) t ctx =
  let (lv, ctx0) = matchPattern p t ctx in
  (lv, ctx0 { constraints = (stripExpRec t, typ):(constraints ctx0) })
-- Not necessary, but avoid generation of useless type variables and constraints
matchPattern (PPair p1 p2) (TTensor t1 t2) ctx =
  let (lv1, ctx1) = matchPattern p1 t1 ctx in
  let (lv2, ctx2) = matchPattern p2 t2 ctx1 in
  (lv1 ++ lv2, ctx2)
matchPattern (PPair p1 p2) t ctx =
  let (x, ctx0) = freshName ctx in
  let (y, ctx1) = freshName ctx0 in
  let (lv1, ctx2) = matchPattern p1 (TVar x) ctx1 in
  let (lv2, ctx3) = matchPattern p2 (TVar y) ctx2 in
  (lv1 ++ lv2, ctx3 { constraints = (t, TTensor (TVar x) (TVar y)):(constraints ctx3) })

-- Basic gates types
basicGates :: [(String, Scheme)]
------------------------------
basicGates =
  [ ("H", ([], TCirc TQBit TQBit)),
    ("NOT", ([], TCirc TQBit TQBit)),
    ("S", ([], TCirc TQBit TQBit)),
    ("T", ([], TCirc TQBit TQBit)),
    ("INIT0", ([], TCirc TUnit TQBit)),
    ("INIT1", ([], TCirc TUnit TQBit)),
    ("TERM0", ([], TCirc TQBit TUnit)),
    ("TERM1", ([], TCirc TQBit TUnit)),
    ("CNOT", ([], TCirc (TTensor TQBit TQBit) (TTensor TQBit TQBit))) ]


-- Create a base context
newContext :: Context
---------------------
newContext =
  Ctx {
    extent = extentUnknown,
    bindings = fromList basicGates,
    constraints = [],
    vars = varSet
  }


-- Typing scheme : on the left, variable to instanciate, on the right a principal type
type Scheme = ([String], Type)

-- Given a typing scheme, and a set of fresh type variables, generate as many type variables as demanded by the scheme
instanciate :: Scheme -> Context -> (Type, Context)
-----------------------------------------------------
instanciate ([], t) ctx = (t, ctx)
instanciate (fv, t) ctx =
  Data.List.foldl (\(t, ctx) x -> let (nv, ctx') = freshName ctx in
                                  (subst x (TVar nv) t, ctx')) (t, ctx) fv



-----------------------------
-- Constraint typing rules --

-- Inputs an expression and a context (devoid of all constraints)
-- Outputs a type, and the new context
constraintTyping :: Expr -> Context -> (Type, Context) 

-- Located expressions
constraintTyping (ELocated e ex) ctx =
  constraintTyping e (ctx { extent = ex })

-- Constraints : add a constraint binding the inferred type, and the given one
-- RULE IS : INFERRED TO THE RIGHT, GIVEN TO THE LEFT
constraintTyping (EConstraint e t) ctx =
  let (t', ctx') = constraintTyping e ctx in
  (t', ctx' { constraints = (stripExpRec t, t'):(constraints ctx') })

-- Rule (axc)
constraintTyping (EVar x) ctx =
  case Data.Map.lookup x $ bindings ctx of
  Just t -> let (v, ctx') = instanciate t ctx in
            (v, ctx')
  Nothing -> error ("At extent " ++ (show $ extent ctx) ++ " -- Unbound variable " ++ x)

-- Rule (unit)
constraintTyping EUnit ctx =
  (TUnit, ctx)

-- Rule (lambda)  -- Only one since ! are ignored
constraintTyping (EFun p e) ctx =
  let (t1, ctx0) = bindPattern p ctx in
  let (t2, ctx1) = constraintTyping e ctx0 in
  (TArrow t1 t2, ctx1)

-- Rule (rev)
constraintTyping (EApp (ELocated ERev _) e) ctx =
  constraintTyping (EApp ERev e) ctx
constraintTyping (EApp ERev e) ctx =
  let (t, ctx0) = constraintTyping e ctx in
  -- By the typing rule, e must be of type circ (A, B)
  -- A constraint t = circ x y is added
  let (x, ctx1) = freshName ctx0 in
  let (y, ctx2) = freshName ctx1 in
  (TCirc (TVar y) (TVar x), ctx2 { constraints = (t, TCirc (TVar x) (TVar y)):(constraints ctx2) })

-- Rule (box1) -- = rule (box2) since all ! annotations are removed
constraintTyping (EApp (ELocated (EBox typ) ex) e) ctx =
  constraintTyping (EApp (EBox typ) e) ctx
constraintTyping (EApp (EBox typ) e) ctx =
  let (t, ctx0) = constraintTyping e ctx in
  -- By the typing rule, e must be of type typ -> B
  -- A new constraint is generated : t = typ -> x
  let (x, ctx1) = freshName ctx0 in
  (TCirc typ (TVar x), ctx1 { constraints = (t, TArrow typ (TVar x)):(constraints ctx1) }) 

-- Rule (app)
constraintTyping (EApp e1 e2) ctx =
  -- First type each expression
  let (t1, ctx1) = constraintTyping e1 ctx in
  let (t2, ctx2) = constraintTyping e2 (ctx { vars = vars ctx1 }) in
  -- By the typing rule, there musts exists a type x such that
  -- t1 = t2 -> x
  let (x, ctx3) = freshName ctx2 in
  (TVar x, ctx3 { constraints = [(t1, TArrow t2 (TVar x))] ++ (constraints ctx3) ++ (constraints ctx1) })

-- Rule (bool)   -- Includes rules (true) and (false)
constraintTyping (EBool _) ctx =
  (TBool, ctx)

-- Rule (pair-i)
constraintTyping (EPair e1 e2) ctx =
  let (t1, ctx1) = constraintTyping e1 ctx in
  let (t2, ctx2) = constraintTyping e2 (ctx { vars = vars ctx1}) in
  (TTensor t1 t2, ctx2 { constraints = (constraints ctx1) ++ (constraints ctx2) })

-- Rule (if)
constraintTyping (EIf e1 e2 e3) ctx =
  let (t1, ctx1) = constraintTyping e1 ctx in
  let (t2, ctx2) = constraintTyping e2 (ctx { vars = vars ctx1 }) in
  let (t3, ctx3) = constraintTyping e3 (ctx { vars = vars ctx2 }) in
  (t2, ctx3 { constraints = (constraints ctx1) ++
                            (constraints ctx2) ++
                            (constraints ctx3) ++ [(t1, TBool), (t2, t3)] })

-- Rule (unbox)
constraintTyping (EUnbox e) ctx =
  let (t, ctx0) = constraintTyping e ctx in
  -- By the typing rule, e must be of type circ (A, B)
  -- A constraint is generated : t = circ x y
  let (x, ctx1) = freshName ctx0 in
  let (y, ctx2) = freshName ctx1 in
  (TArrow (TVar x) (TVar y), ctx2 { constraints = (t, TCirc (TVar x) (TVar y)):(constraints ctx2) })  

-- Rule (let)  -- More general than (pair-e)
constraintTyping (ELet p e1 e2) ctx =
  -- Remember the first unused type variable, will be useful to tell if
   -- a type variable existed in the context before or not
  let firstUnused = extractId $ head $ vars ctx in
  -- Type the matched expression
  let (t1, ctx1) = constraintTyping e1 ctx in
  -- Match the pattern, eventually generating new type variables and new constraints
  let (lv, ctx2) = matchPattern p t1 ctx1 in  
  -- Unify the whole
  let sub = unify $ constraints ctx2 in
  -- Identy all the principal types of the free variables of the pattern
  let ptypes = Data.List.map (\(x, t) -> (x, appSubst sub t)) lv in
  -- Bind them in the current typing environment
  -- May introduce polymorphic types to sub-branches that are values
  -- Ie : instead of rejecting <f, a b> (not a value), one could set a polymporphic type for f at least
  let ctx3 = if isValue e1 then
               Data.List.foldl (\c (x, t) ->
                                 let vs = extractVariables t in
                                 -- All the type variables that were already in the typing context before can't be instanciated
                                 -- This is decided by comparing the type variable to the first unused registered above
                                 let fvs = Data.List.filter (\v -> extractId v >= firstUnused) vs in
                                 c { bindings = Data.Map.insert x (fvs, t) $ bindings c })
                               (ctx { vars = vars ctx2 }) ptypes
             else
               Data.List.foldl (\ctx (x, t) -> ctx { bindings = Data.Map.insert x ([], t) $ bindings ctx })
                               (ctx { vars = vars ctx2 }) ptypes
  in constraintTyping e2 ctx3

-- Remaining cases
constraintTyping e ctx =
  error ("Not implemented yet : " ++ show e ++ " -- at extent " ++ (show $ extent ctx))

---------------------------
-- unification algorithm --

unify :: [(Type, Type)] -> Map String Type

-- Empty constraints
unify [] = empty
-- Trivial
unify ((s, t):c) =
  if s == t then
    unify c
  else
    caseXT s t c

-- Case where s is a type variable
caseXT s t c =
  case s of
  TVar x ->
    if elem x (extractVariables t) then
      caseSX s t c
    else
      Data.Map.insert x t (unify (Data.List.map (\(a, b) -> (subst x t a, subst x t b)) c))
  _ ->
    caseSX s t c

-- Case where t is a type variable
caseSX s t c =
  case t of
  TVar x ->
    if elem x (extractVariables s) then
      caseAA s t c
    else
      Data.Map.insert x s (unify (Data.List.map (\(a, b) -> (subst x s a, subst x s b)) c))
  _ ->
    caseAA s t c

-- Other cases
caseAA s t c =
  case (s, t) of
  (TLocated s' _, _) ->
      unify ((s', t):c)
  (_, TLocated t' _) ->
      unify ((s, t'):c)
  (TArrow t1 t2, TArrow s1 s2) ->
      unify ((t1, s1):(t2, s2):c)
  (TTensor t1 t2, TTensor s1 s2) ->
      unify ((t1, s1):(t2, s2):c)
  (TCirc t1 t2, TCirc s1 s2) ->
      unify ((t1, s1):(t2, s2):c)
  _ ->
      error ("Unification failed\n-- Expected type : " ++ show s ++ "\n" ++
                                 "-- Actual type   : " ++ show t)


-----------------------------------------------
-- Final algorithm : put everything together --

-- Computes the principal type of the expression
principalType :: Expr -> Type
-----------------------------
principalType e =
  let (t, ctx) = constraintTyping e newContext in
  let sub = unify $ constraints ctx in
  appSubst sub t

{- Will do that when I have unique identifiers
-- Computes and returns the principal types of all the variables declared in the expression
allPrincipalTypes :: Expr -> Map String Type
--------------------------------------------
allPrincipalTypes e =
  let (_, ctx) = constraintTyping e newContext in
  let sub = unify $ constraints ctx in
  Data.Map.map (\(_, t) -> appSubst sub)
-}
