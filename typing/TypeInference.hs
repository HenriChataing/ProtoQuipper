module TypeInference where

import Classes
import Utils
import Localizing

import CoreSyntax

import Contexts

import Subtyping
import Ordering

import Data.List as List
import Data.Sequence as Seq
import Data.Array as Array
import qualified Data.Map as Map
import qualified Data.Set as Set

-----------------------------------------------------------------
-----------------------------------------------------------------

-- Build all the deriving constraints
build_constraints :: Expr -> Type -> State ConstraintSet

-- Unit typing rule
{-
    -----------------------------------
      !I G  |- * : !n T    [{1 <= I}]
-} 

build_constraints EUnit t = do
  ann <- context_annotation
  return ([(t, TUnit)], List.map (\(_, f) -> (1, f)) ann)
  
-- Var typing rule
{-
     
   ---------------------------------------------
     !IG, t : T |- t : U    [{T <: U, 1 <= I}]
-}

build_constraints (EVar x) u = do
  t <- find_var x
  ann <- context_annotation
  ann' <- return $ List.deleteBy (\(x, _) (y, _) -> x == y) (x, 0) ann
  return ([(t, u)], List.map (\(_, f) -> (1, f)) ann')

-- App typing rule
{-
     G1, !ID |- t : a -> T  [L]      G2, !ID |- u : a  [L']
   -----------------------------------------------------------
         G1, G2, !ID |- t u : T  [L u L' u {1 <= I}]
-}

build_constraints (EApp t u) b = do
  a <- new_type
  -- Extract the free variables of t and u
  fvt <- return $ free_var t
  fvu <- return $ free_var u
  -- Filter on the free variables of t and type t
  non_fvt <- filter_by (\x -> List.elem x fvt)
  (lcons, fcons) <- build_constraints t (TArrow a b)
  -- Filter on the free variables of u and type u
  Contexts.union non_fvt
  non_fvu <- filter_by (\x -> List.elem x fvu)
  (lcons', fcons') <- build_constraints u a
  -- Reset the environment, and add the last constraints
    -- Need to perform : FV(t) + FV(u) (disjoint union)
  Contexts.union non_fvu
  dis_union <- return $ List.union (fvt \\ fvu) (fvu \\ fvt)
  ann <- context_annotation
  ann_cons <- return $ List.foldl (\cl (x, f) -> if List.elem x dis_union then cl
                                                 else (1, f):cl) [] ann
  
  return (lcons' ++ lcons, fcons' ++ fcons ++ ann_cons)

-- Lambda typing rule
{-
     !IG, x : a |- t : b  [L]
   ---------------------------------------------
     !IG |- \x.t : !n(a -> b)  [L u {n <= Ii}]
-}

build_constraints (EFun x e) t = do
  a <- new_annotated_type
  b <- new_type
  n <- fresh_flag
  ann <- context_annotation
  -- Bind x in the context
  bind_var x a
  -- Type the expression e
  (lcons, fcons) <- build_constraints e b
  -- Build the context constraints : n <= I
  ann_cons <- return $ List.map (\(_, f) -> (n, f)) ann
  -- Remove x from the context
  delete_var x

  return ((TExp n $ TArrow a b, t):lcons, fcons ++ ann_cons)

-- Tensor intro typing rule
{-
     G1, !ID |- t : a  [L]           G2, !ID |- u : b  [L']
   ----------------------------------------------------------
     G1, G2, !ID |- <t, u> : a * b   [L u L' u {1 <= I}]
-}

build_constraints (EPair t u) typ = do
  a <- new_type
  b <- new_type
  -- Extract the free variables of t and u
  fvt <- return $ free_var t
  fvu <- return $ free_var u
  -- Filter on the free variables of t and type t
  non_fvt <- filter_by (\x -> List.elem x fvt)
  (lcons, fcons) <- build_constraints t a
  -- Filter on the free variables of u and type u
  Contexts.union non_fvt
  non_fvu <- filter_by (\x -> List.elem x fvu)
  (lcons', fcons') <- build_constraints u b
  -- Reset the environment, and add the last constraints
    -- Need to perform : FV(t) + FV(u) (disjoint union)
  Contexts.union non_fvu
  dis_union <- return $ List.union (fvt \\ fvu) (fvu \\ fvt)
  ann <- context_annotation
  ann_cons <- return $ List.foldl (\cl (x, f) -> if List.elem x dis_union then cl
                                                 else (1, f):cl) [] ann
  
  return (lcons' ++ lcons ++ [(TTensor a b, typ)], fcons' ++ fcons ++ ann_cons)


-- Tensor elim typing rule
{-
     G1, !ID |- t : !n<a, b>  [L]    G2, !ID, x : !na, y : !nb |- u : T  [L']
   -----------------------------------------------------------------------------
     G1, G2, !ID |- let <x, y> = t in u : T    [L u L' u {1 <= I}]
-}

build_constraints (ELet x y t u) typ = do
  a <- new_type
  b <- new_type
  n <- fresh_flag
  -- Extract the free variables of t and u
  fvt <- return $ free_var t
  fvu <- return $ free_var u
  -- Filter on the free variables of t and type t
  non_fvt <- filter_by (\x -> List.elem x fvt)
  (lcons, fcons) <- build_constraints t (TExp n (TTensor a b))
  -- Filter on the free variables
  Contexts.union non_fvt
  non_fvu <- filter_by (\x -> List.elem x fvu)
  -- Add x and y to the context
  bind_var x (TExp n a)
  bind_var y (TExp n b)
  -- Type u
  (lcons', fcons') <- build_constraints u typ
  -- Clean the context
  delete_var x
  delete_var y
  Contexts.union non_fvu
  -- Generate the flag constraints for the intersection
  dis_union <- return $ List.union (fvt \\ fvu) (fvu \\ fvt)
  ann <- context_annotation
  ann_cons <- return $ List.foldl (\cl (x, f) -> if List.elem x dis_union then cl
                                                 else (1, f):cl) [] ann
  
  return (lcons' ++ lcons, fcons' ++ fcons ++ ann_cons)

--------------------------------------------------------------------------
--------------------------------------------------------------------------

-- Break composite constrainst of the form :
  -- T -> U <: T' -> U'
  -- ! T <: ! U

break_composite :: ConstraintSet -> State ConstraintSet

-- Nothing to do
break_composite ([], lc) = return ([], lc)

-- Break constraints
  -- T -> U <: T' -> U' 
-- Into
  -- T' <: T && U <: U'
break_composite ((TArrow t u, TArrow t' u'):lc, fc) = do
  break_composite ((t', t):(u, u'):lc, fc)

-- Break constraints
  -- T * U <: T' * U'
-- Into
  -- T <: T' && U <: U'

break_composite ((TTensor t u, TTensor t' u'):lc, fc) = do
  break_composite ((t, t'):(u, u'):lc, fc)

-- Break constraints
  -- !n T <: !m U
-- Into
  -- T <: U && m <= n
break_composite ((TExp n t, TExp m u):lc, fc) = do
  break_composite ((t, u):lc, (m, n):fc)

-- Break constraints
  -- !n T <: U
-- Into
  -- T <: U
break_composite (c@(TExp _ _, TVar _):lc, fc) = do
  (lc', fc') <- break_composite (lc, fc)
  return (c:lc', fc')

break_composite ((TExp _ t, u):lc, fc) = do
  break_composite ((t, u):lc, fc)

-- Break constraints
  -- T <: !n U
-- Into
  -- T <: U && n <= 0
break_composite (c@(TVar _, TExp _ _):lc, fc) = do
  (lc', fc') <- break_composite (lc, fc)
  return (c:lc', fc')

break_composite ((t, TExp n u):lc, fc) = do
  break_composite ((t, u):lc, (n, 0):fc)

-- Other non composite constraints
break_composite (c:lc, fc) = do
  (lc', fc') <- break_composite (lc, fc)
  return (c:lc', fc')

-------------------------------------- UNIFICATION -----------------------------------------------------

-- Sort constraints that have a as right hand side
with_rhs :: Variable -> [LinearConstraint] -> State ([LinearConstraint], [LinearConstraint])

-- Sort constraints that have a as left hand side
with_lhs :: Variable -> [LinearConstraint] -> State ([LinearConstraint], [LinearConstraint])
-----------------------------------------------------------------------------
with_rhs x lc = do
  return $ List.partition (\(_, u) -> case u of
                                        TVar y -> x == y
                                        _ -> False) lc
with_lhs x lc = do
  return $ List.partition (\(t, _) -> case t of
                                        TVar y -> x == y
                                        _ -> False) lc

-- Break a composite against a variable
break_var :: LinearConstraint -> State ([Variable],ConstraintSet)
-------------------------------------------------------------------------
{- Break the constraint
     x <: t -> u
   into
     x := !n (t' -> u')
     t <: t'
     u' <: u
-}

break_var (TVar x, TArrow t u) = do
  t' <- fresh_type
  u' <- fresh_type
  n <- fresh_flag

  mapsto x (TExp n $ TArrow (TVar t') (TVar u'))
  return ([t', u'], ([ (t, TVar t'), (TVar u', u) ], []))

{- Break the constraint
     t -> u <: x
   into
     x := t' -> u'
     t' <: t
     u <: u'
-}

break_var (TArrow t u, TVar x) = do
  t' <- fresh_type
  u' <- fresh_type

  mapsto x (TArrow (TVar t') (TVar u'))
  return ([t', u'], ([ (TVar t', t), (u, TVar u') ], []))

---

{- Break the constraint
     x <: t * u
   into
     x := !n (t' * u')
     t' <: t
     u' <: u
-}

break_var (TVar x, TTensor t u) = do
  t' <- fresh_type
  u' <- fresh_type
  n <- fresh_flag

  mapsto x (TExp n $ TTensor (TVar t') (TVar u'))
  return ([t', u'], ([ (TVar t', t), (TVar u', u) ], []))

{- Break the constraint
     t * u <: x
   into
     x := t' * u'
     t <: t'
     u <: u'
-}

break_var (TTensor t u, TVar x) = do
  t' <- fresh_type
  u' <- fresh_type

  mapsto x (TTensor (TVar t') (TVar u'))
  return ([t', u'], ([ (t, TVar t'), (u, TVar u') ], []))

---

{- Break the constraint
     x <: !n t
   into
     x := !m t'
     t' <: t
     n <= m
-}

break_var (TVar x, TExp n t) = do
  t' <- fresh_type
  m <- fresh_flag

  mapsto x (TExp m (TVar t'))
  return ([t'], ([ (TVar t', t) ], [ (n, m) ]))

{- Break the constraint
     !n t <: x
   into
     x := !m t'
     t <: t'
     m <= n
-}

break_var (TExp n t, TVar x) = do
  t' <- fresh_type
  m <- fresh_flag

  mapsto x (TExp m (TVar t'))
  return ([t'], ([ (t, TVar t') ], [ (m, n) ]))

---

{- Break the constraint
     x <: T
   into
     x := T
-}

break_var (TUnit, TVar x) = do
  mapsto x TUnit
  return ([], ([], []))

{- Break the constraint
     x <: T
   into
     x := T
-}

break_var (TVar x, TUnit) = do
  mapsto x TUnit
  return ([], ([], []))

break_var (TVar _, TVar _) = do
  fail "Unwelcomed atomic constraint"


-- Unification algorithm :
  -- Each step eliminates a variable
  -- Variables are taken youngest first
  -- If we get the following case :
    -- x is lhs/rhs of only one constraint -> break that constraint and substitute x
    -- x is lhs/rhs of several constraints -> generate the constraints rhs <: lhs and eliminate x

unify :: ConstraintSet -> State ConstraintSet
----------------------------------------------------------------------------
unify (lc, fc) = do
  -- Recursive check
  stop <- null_heuristic
  
  if stop then
    return (lc, fc)
  else do
      x <- fitting_var 

      -- Identify the constraint with x as left or right hand side
      (lhs, non_lhs) <- with_lhs x lc
      (rhs, non_rhs) <- with_rhs x non_lhs

      -- Check the next action
      case (List.partition atomic lhs, List.partition atomic rhs) of

        -- No semi-composite constraints
        ((atoml, []), (atomr, [])) -> do
            unify (lc, fc)

        -- Semi composite on the right
        ((atoml, []), (atomr, c:cset)) -> do
            -- Break the semi-composite constraint
            (nvar, (lc', fc')) <- break_var c
            xt <- appmap x
            -- Substitute x
            atoml' <- return $ List.map (\(_, u) -> (xt, u)) atoml
            atomr' <- return $ List.map (\(t, _) -> (t, xt)) atomr
            cset' <- return $ List.map (\(t, _) -> (t, xt)) cset
            -- Break the composite constraints in cset'
            (cset'', fc'') <- break_composite (cset', fc ++ fc')
            -- Add the new variables to the heuristic
            fvtl <- return $ List.concat $ List.map (\(_, u) -> free_var u) atoml
            fvtr <- return $ List.concat $ List.map (\(t, _) -> free_var t) atomr
            
            insert_all_after nvar (fvtl ++ fvtr)
            -- Rec call
            unify (non_rhs ++ lc' ++ atoml' ++ atomr' ++ cset'', fc'')

        -- Semi composite on the left
        ((atoml, c:cset), (atomr, natomr)) -> do
            -- Break the semi-composite constraint
            (nvar, (lc', fc')) <- break_var c
            xt <- appmap x
            -- Substitute x
            atoml' <- return $ List.map (\(_, u) -> (xt, u)) atoml
            atomr' <- return $ List.map (\(t, _) -> (t, xt)) atomr
            cset' <- return $ List.map (\(_, u) -> (xt, u)) cset
            natomr' <- return $ List.map (\(t, _) -> (t, xt)) natomr
            -- Break the composite constraints
            (cset'', fc'') <- break_composite (cset' ++ natomr', fc ++ fc')
             -- Add the new variables to the heuristic
            fvtl <- return $ List.concat $ List.map (\(_, u) -> free_var u) atoml
            fvtr <- return $ List.concat $ List.map (\(t, _) -> free_var t) atomr
            
            insert_all_after nvar (fvtl ++ fvtr)
            -- Rec call
            unify (non_rhs ++ lc' ++ atoml' ++ atomr' ++ cset'', fc'')

-- Flag unification

-- Set a flag value
set_flag :: Flag -> Int -> Map.Map Flag Int -> State (Map.Map Flag Int)
-----------------------------------------------------------------------
set_flag f n val = do
  case Map.lookup f val of
    Just m | m == n -> do return val
           | otherwise -> do fail "Unsolvable flag constraint set"
    _ -> do return $ Map.insert f 1 val 

-- Solve the constraint set
solve_annotation :: [FlagConstraint] -> State (Map.Map Flag Int)
----------------------------------------------------------------
solve_annotation fc = do
  -- Empty valuation
  valuation <- return $ Map.empty
  -- Elimination of trivial constraints f <= 1 and 0 <= f
  fc' <- return $ List.filter (\(m, n) -> (m /= 0 && n /= 1)) fc

  -- Application of the constraints 1 <= f and f <= 0
  (fc_set, fc_impl) <- return $ List.partition (\(m, n) -> (m == 1 || n == 0)) fc'
  valuation <- List.foldl (\val c -> case c of
                                       (1, 0) -> do
                                           fail "Absurd constraint 1 <= 0"

                                       (n, 0) -> do
                                           v <- val
                                           set_flag n 0 v

                                       (1, n) -> do
                                           v <- val
                                           set_flag n 1 v

                                       ) (return valuation) fc_set

  -- Application of the constraints f <= g
  valuation <- List.foldl (\val (n, m) -> do
                               v <- val
                               case Map.lookup n v of
                                 Just 1 -> do
                                     set_flag m 1 v
                                 _ -> do
                                     return v) (return valuation) fc_impl

  return valuation

