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

-- Instanciation of model types
  -- The bang annotations of the model are ignored
model_of :: Type -> State Type
map_to_model :: Variable -> Type -> State Type
-------------------------------------------------------------------------
model_of TUnit = do
  return TUnit

model_of (TArrow t u) = do
  t' <- model_of t
  u' <- model_of u
  n <- fresh_flag
  return $ TExp n $ TArrow t' u'

model_of (TTensor t u) = do
  t' <- model_of t
  u' <- model_of u
  n <- fresh_flag
  return $ TExp n $ TTensor t' u'

model_of (TExp _ t) = do
  model_of t

model_of (TVar _) = do
  x <- fresh_type
  n <- fresh_flag
  -- Add the variable to the list managed by the ordering process
  add_variable x
  return $ TExp n $ TVar x
-------------
map_to_model x t = do
  t' <- model_of t
  mapsto x t'
  return t'

-- Unification algorithm :
  -- Each step eliminates a variable
  -- Variables are taken youngest first
  -- If we get the following case :
    -- x is lhs/rhs of only one constraint -> break that constraint and substitute x
    -- x is lhs/rhs of several constraints -> generate the constraints rhs <: lhs and eliminate x

unify :: ConstraintSet -> State ConstraintSet
---------------------------------------------
unify (lc, fc) = do
  -- Recursive check
  stop <- null_cluster
  
  if stop then
    return (lc, fc)
  else do
      cx <- youngest_variables 

      -- Filter the constraint which have an element of cx as right or left hand side
      (lcx, non_lcx) <- return $ List.partition (\c -> case c of 
                                                          (TVar x, _) -> List.elem x cx
                                                          (_, TVar y) -> List.elem y cx) lc
        
      -- Log
      logx <- return $ List.foldl (\s c -> "(" ++ pprint c ++ ") " ++ s) "" lcx
      lognonx <- return $ List.foldl (\s c -> "(" ++ pprint c ++ ") " ++ s) "" non_lcx
      new_log logx
      new_log lognonx
                                             
      -- Filter the atomic constraints
      (atomx, natomx) <- return $ List.partition atomic lcx

      -- Check the next action
      case (atomx, natomx) of

        -- No semi-composite constraints : trivial solution with x1 = .. = xn,  unify the rest
        (atomx, []) -> do
            (non_lcx', fc') <- unify (non_lcx, fc)
            return (non_lcx' ++ atomx, fc')

        -- Semi-composite constraints :
           -- Pick up a sample type, and map all variables of cx to an instance of this type
        (atomx, cset) -> do
           {- onesided <- return $ one_sided cset
            -- If all the constraints are one-sided, make the approximation : x1 = .. = xn
            cset <- if onesided then do
                      cxh <- return $ List.head cx
                      List.foldl (\rec x -> do
                                      rec
                                      mapsto x $ TVar cxh) (return ()) $ List.tail cx
                      return $ List.map (\c -> case c of
                                                 (TVar _, t) -> (TVar cxh, t)
                                                 (t, TVar _) -> (t, TVar cxh)) cset
                    else do
                      return cset -}

            -- If all the constraints are chained as : T <: x1 <: .. <: xn <: U, make the approximation x1 = .. = xn = T
            (ischain, sorted) <- return $ chain_constraints lcx
            
            leftend <- return $ fst $ List.head sorted
            rightend <- return $ snd $ List.last sorted

            if ischain then do
              new_log "CHAINED"
              -- Map x1 .. xn to T or U
              case (leftend, rightend) of
                (TVar x, _) -> do
                    List.foldl (\rec x -> do
                                  rec
                                  mapsto x rightend) (return ()) cx
                    -- Unify the rest
                    unify (non_lcx, fc)
                    
                (_, TVar x) -> do
                    List.foldl (\rec x -> do
                                  rec
                                  mapsto x leftend) (return ()) cx
                    -- Unify the rest
                    unify (non_lcx, fc)

                _ -> do
                    List.foldl (\rec x -> do
                                  rec
                                  mapsto x leftend) (return ()) cx

                    (cset', fc') <- break_composite ([(leftend, rightend)], fc)
                    register_constraints cset'
                    -- Unify the rest
                    unify (cset' ++ non_lcx, fc')

            else do           
              new_log "UNCHAINED"
              model <- return $ constraint_unifier cset

              new_log $ pprint model

            
              List.foldl (\rec x -> do
                             rec
                             _ <- map_to_model x model
                             return ()) (return ()) cx
            
              -- Rewrite and reduce the atomic constraints
              atomx' <- List.foldl (\rec (TVar x, TVar y) -> do
                                      (lr, fr) <- rec
                                      xt <- appmap x
                                      yt <- appmap y
                                      (lr', fr')  <- break_composite ([(xt, yt)], fr)
                                      return (lr' ++ lr, fr')) (return (non_lcx, fc)) atomx

              -- Rewrite and reduce the remaining constraints
              (cset', fc'') <- List.foldl (\rec c -> do
                                     (lr, fr) <- rec
                                     c' <- case c of
                                             (TVar x, t) -> do
                                                 xt <- appmap x
                                                 return (xt, t)
                                             (t, TVar x) -> do
                                                 xt <- appmap x
                                                 return (t, xt)
                                     (lr', fr') <- break_composite ([c'], fr)
                                     return (lr' ++ lr, fr')) (return atomx') cset
              
              -- Register the new relations defined by those constraints
              register_constraints cset'

              -- Unifcation of the remaining
              unify (cset', fc'')

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

