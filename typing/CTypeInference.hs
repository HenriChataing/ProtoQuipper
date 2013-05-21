module CTypeInference where

import qualified Syntax as S
import CoreSyntax
import TransCore

import Localizing
import Contexts
import Utils

import Gates

import Data.Map
import Data.List

-- Create a base context (add the basic gates to the empty context)
newContext :: Context
---------------------
newContext =
  Data.List.foldl (\ctx (g, t) ->
                     let (ig, ctx0) = register g ctx in
                     let (ft, ctx1) = translateType t ctx0 in
                     ctx1 { bindings = Data.Map.insert ig ([], ft) $ bindings ctx1 }) emptyContext typingEnvironment

-----------------------------
-- Constraint typing rules --

-- Inputs an expression and a context (devoid of all constraints)
-- Outputs a type, and the new context

-- Constrainttyping must enforce several properties :
        -- The bindings must be the same at the beginning and at the end of the function application
        -- The input context must not contain any constraints

constraintTyping :: Expr -> Context -> (FType, Context) 

-- Located expressions
constraintTyping (ELocated e ex) ctx =
  constraintTyping e (ctx { extent = ex })

-- Constraints : add a constraint binding the inferred type, and the given one
-- RULE IS : INFERRED TO THE RIGHT, GIVEN TO THE LEFT
constraintTyping (EConstraint e t) ctx =
  let (t', ctx0) = constraintTyping e ctx in
  (t, ctx0 { tConstraints = (cons t t' $ extent ctx):(tConstraints ctx0) })

-- Rule (axc)
constraintTyping (EVar x) ctx =
  case Data.Map.lookup (uid x) $ bindings ctx of
  Just t -> instanciate t ctx
  Nothing -> error ("Error : Scope analysis should have ruled out such errors -- Still : x" ++ (subscript $ show $ uid x) ++
                                                                                       " @ " ++ (show $ ext x))

-- Rule (unit)
constraintTyping EUnit ctx =
  let (f, ctx0) = freshFlag ctx in
  (FTyp TUnit f, ctx0)

-- Rule (lambda)  -- Only one since ! are ignored
constraintTyping (EFun p e) ctx =
  let (t1, ctx0) = bindPattern p ctx in
  let (t2, ctx1) = constraintTyping e ctx0 in
  let (f, ctx2) = freshFlag ctx1 in
  (FTyp (TArrow t1 t2) f, ctx2 { bindings = bindings ctx })


-- Rule (rev)
constraintTyping (EApp (ELocated ERev _) e) ctx =
  constraintTyping (EApp ERev e) ctx
constraintTyping (EApp ERev e) ctx =
  -- ctx is devoid of any type constraints
  let (t, ctx0) = constraintTyping e ctx in
  -- By the typing rule, e must be of type circ (A, B)
  -- A constraint t = circ x y is added
  let (nt, ctx1) = newType ctx0 in
  let (nu, ctx2) = newType ctx1 in
  let (f, ctx3) = freshFlag ctx2 in
  let (g, ctx4) = freshFlag ctx3 in
  -- Add constraints of e and newly generated one
  -- The context returned by constraintTyping applied on e has already the same bindings as ctx, so no need to enforce that here
  (FTyp (TCirc nu nt) f, ctx4 { tConstraints = [(cons t (FTyp (TCirc nt nu) g) $ extent ctx)] ++ (tConstraints ctx0) })

-- Rule (box1) -- = rule (box2) since all ! annotations are removed
constraintTyping (EApp (ELocated (EBox typ) _) e) ctx =
  constraintTyping (EApp (EBox typ) e) ctx
constraintTyping (EApp (EBox typ) e) ctx =
  let (t, ctx0) = constraintTyping e ctx in
  -- By the typing rule, e must be of type typ -> B
  -- A new constraint is generated : t = typ -> B
  -- The whole expression is of type circ typ B
  let (u, ctx1) = newType ctx0 in
  let (f, ctx2) = freshFlag ctx1 in
  let (g, ctx3) = freshFlag ctx2 in
  -- Add the constraints of e and the newly generated ones
  (FTyp (TCirc typ u) f, ctx3 { tConstraints = [(cons t (FTyp (TArrow typ u) g) $ extent ctx)] ++ (tConstraints ctx0) }) 

-- Rule (app)
constraintTyping (EApp e1 e2) ctx =
  -- At this point, ctx shouldn't contain any type constraints
  let (t1, ctx1) = constraintTyping e1 ctx in
  -- The type constraints of e1 and e2 are separate, the bindings are already those of ctx
  let (t2, ctx2) = constraintTyping e2 (ctx1 { tConstraints = [] }) in
  -- By the typing rule, there musts exists a type x such that t1 = t2 -> x
  let (u, ctx3) = newType ctx2 in
  let (f, ctx4) = freshFlag ctx3 in
  -- Cumulate the constraints of e1 e2 and the newly introduced one
  -- The bindings are already those of ctx
  (u, ctx4 { tConstraints = [(cons t1 (FTyp (TArrow t2 u) f) $ extent ctx)] ++ (tConstraints ctx1) ++ (tConstraints ctx2) })

-- Rule (bool) :   Includes rules (true) and (false)
constraintTyping (EBool _) ctx =
  let (f, ctx0) = freshFlag ctx in
  (FTyp TBool f, ctx0)

-- Rule (pair-i)
constraintTyping (EPair e1 e2) ctx =
  -- At this point, there shoulnd't be any constraint in ctx
  let (t1, ctx1) = constraintTyping e1 ctx in
  -- Enforce empty constraint set on function call
  let (t2, ctx2) = constraintTyping e2 (ctx1 { tConstraints = [] }) in
  let (f, ctx3) = freshFlag ctx2 in
  -- Constraints are those of e1 and e2
  (FTyp (TTensor t1 t2) f, ctx3 { tConstraints = (tConstraints ctx1) ++ (tConstraints ctx2) })

-- Rule (if)
constraintTyping (EIf e1 e2 e3) ctx =
  let (t1, ctx1) = constraintTyping e1 ctx in
  let (t2, ctx2) = constraintTyping e2 (ctx1 { tConstraints = [] }) in
  let (t3, ctx3) = constraintTyping e3 (ctx2 { tConstraints = [] }) in
  let (f, ctx4) = freshFlag ctx3 in
  -- Constraints are those of e1, e2 and e3, plus t2 = t3 and t1 = Bool
  (t2, ctx4 { tConstraints = [(cons t1 (FTyp TBool f) $ extent ctx1),
                              (cons t2 t3 $ extent ctx)] ++ (tConstraints ctx1)
                                                         ++ (tConstraints ctx2)
                                                         ++ (tConstraints ctx3) })

-- Rule (unbox)
constraintTyping (EUnbox e) ctx =
  let (t, ctx0) = constraintTyping e ctx in
  -- By the typing rule, e must be of type circ (A, B)
  -- A constraint is generated : t = circ x y
  -- The return type is : x -> y
  let (x, ctx1) = newType ctx0 in
  let (y, ctx2) = newType ctx1 in
  let (f, ctx3) = freshFlag ctx2 in
  let (g, ctx4) = freshFlag ctx3 in
  (FTyp (TArrow x y) f, ctx4 { tConstraints = (cons t (FTyp (TCirc x y) g) $ extent ctx):(tConstraints ctx0) })

-- Rule (let)  -- More general than (pair-e)
constraintTyping (ELet p e1 e2) ctx =
  -- Remember the first unused type variable, will be useful to tell if
   -- a type variable existed in the context before or not
  let firstUnused = typeId ctx in
  -- Type the matched expression
  let (t1, ctx1) = constraintTyping e1 ctx in
  -- Match the pattern, eventually generating new type variables and new constraints
  let (lv, ctx2) = matchPattern p t1 ctx1 in  
  -- Unify the whole
  let (sub, ctx3) = unify ctx2 in
  -- Identify all the principal types of the free variables of the pattern
  let ptypes = Data.List.map (\(x, t) -> (x, appSubst sub t)) lv in
  -- Bind them in the current typing environment
  -- May introduce polymorphic types to sub-branches that are values
  -- Ie : instead of rejecting <f, a b> (not a value), one could set a polymporphic type for f at least
  let ctx4 = if isValue e1 then
               Data.List.foldl (\c (x, t@(FTyp tf _)) ->
                                 let vs = extractVariables tf in
                                 -- All the type variables that were already in the typing context before can't be instanciated
                                 -- This is decided by comparing the type variable to the first unused registered above
                                 let fvs = Data.List.filter (\v -> v >= firstUnused) vs in
                                 c { bindings = Data.Map.insert x (fvs, t) $ bindings c })
                               ctx3 ptypes
             else
               Data.List.foldl (\ctx (x, t) -> ctx { bindings = Data.Map.insert x ([], t) $ bindings ctx })
                               ctx3 ptypes
  in constraintTyping e2 ctx4

-- Remaining cases
constraintTyping e ctx =
  error ("Not implemented yet : " ++ show e ++ " -- at extent " ++ (show $ extent ctx))

---------------------------
-- unification algorithm --

-- Unify the type constraints of the context
-- A substitution is generated, and applied to the context bindingd
-- various flag constraints are generated too
unify :: Context -> (Map Int Type, Context)

-- Empty constraints
unify ctx = 
  case tConstraints ctx of
  [] ->
      (empty, ctx)
  (FTyp s fs, FTyp t ft, ext):c ->
      if (s == t) then
         -- trivial cases : only a flag constraint is generated
         unify (ctx { tConstraints = c, fConstraints = (FEq fs ft):(fConstraints ctx) })
      else
         caseXT s t ext (ctx { tConstraints = c, fConstraints = (FEq fs ft):(fConstraints ctx) })

-- Case where s is a type variable
caseXT :: Type -> Type -> Extent -> Context -> (Map Int Type, Context)
----------------------------------------------------------------------
caseXT s t ext ctx =
  case s of
  TVar x ->
    if elem x (extractVariables t) then
      caseSX s t ext ctx
    else
      let (m, ctx0) = unify (ctx { bindings = Data.Map.map (\(l, u) -> (l, subst x t u)) $ bindings ctx,
                                   tConstraints = Data.List.map (\(a, b, ex) -> (subst x t a, subst x t b, ex)) $ tConstraints ctx }) in
      (Data.Map.insert x t m, ctx0)
  _ ->
    caseSX s t ext ctx

-- Case where t is a type variable
caseSX :: Type -> Type -> Extent -> Context -> (Map Int Type, Context)
----------------------------------------------------------------------
caseSX s t ext ctx =
  case t of
  TVar x ->
    if elem x (extractVariables s) then
      caseAA s t ext ctx
    else
      let (m, ctx0) = unify (ctx { bindings = Data.Map.map (\(l, u) -> (l, subst x s u)) $ bindings ctx,
                                   tConstraints = Data.List.map (\(a, b, ex) -> (subst x s a, subst x s b, ex)) $ tConstraints ctx }) in
      (Data.Map.insert x s m, ctx0)
  _ ->
    caseAA s t ext ctx

-- Other cases
caseAA :: Type -> Type -> Extent -> Context -> (Map Int Type, Context)
----------------------------------------------------------------------
caseAA s t ext ctx =
  case (s, t) of
  (TArrow t1 t2, TArrow s1 s2) ->
      unify (ctx { tConstraints = (t1, s1, ext):(t2, s2, ext):(tConstraints ctx) })
  (TTensor t1 t2, TTensor s1 s2) ->
      unify (ctx { tConstraints = (t1, s1, ext):(t2, s2, ext):(tConstraints ctx) })
  (TCirc t1 t2, TCirc s1 s2) ->
      unify (ctx { tConstraints = (t1, s1, ext):(t2, s2, ext):(tConstraints ctx) })
  _ ->
      error ("In expression : " ++ show ext ++
             "\nUnification failed\n-- Expected type : " ++ show s ++ "\n" ++
                                   "-- Actual type   : " ++ show t)

--- Algorithm
principalType :: S.Expr -> FType
principalType e =
  let (ce, ctx0) = translateExpr e newContext in
  let (t, ctx1) = constraintTyping ce ctx0 in
  let (sub, ctx2) = unify ctx1 in
  appSubst sub t
