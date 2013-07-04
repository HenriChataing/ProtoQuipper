module TypeInference where

import Classes
import Utils
import Localizing

import CoreSyntax

import Contexts
import TypingContext

import Subtyping
import Ordering

import Data.List as List
import Data.Sequence as Seq
import Data.Array as Array
import qualified Data.Map as Map
import qualified Data.Set as Set

-- Build all the deriving constraints
constraint_typing :: TypingContext -> Expr -> Type -> State ConstraintSet

-- Located things
constraint_typing typctx (ELocated e ex) t = do
  set_location ex
  constraint_typing typctx e t

-- Unit typing rule
{-
    -----------------------------------
      !I G  |- * : !n T    [{1 <= I}]
-} 

constraint_typing typctx EUnit t = do
  flags <- context_annotation typctx
  flags_cons <- return $ List.map (\(_, f) -> (1, f)) flags

  return ([NonLinear t (TExp 1 TUnit)], flags_cons)

-- True / False typing rule
{-
   -------------------------------------------
     !I G |- True / False : !n T   [{1 <= I}]
-} 

constraint_typing typctx (EBool _) t = do
  flags <- context_annotation typctx
  flags_cons <- return $ List.map (\(_, f) -> (1, f)) flags

  return ([NonLinear t (TExp 1 TBool)], flags_cons)

-- Var typing rule
{-
   ---------------------------------------------
     !IG, t : T |- t : U    [{T <: U, 1 <= I}]
-}

constraint_typing typctx (EVar x) u = do
  t <- type_of x typctx
  flags <- context_annotation typctx
  flags_nx <- return $ List.deleteBy (\(x, _) (y, _) -> x == y) (x, 0) flags
  flags_cons <- return $ List.map (\(_, f) -> (1, f)) flags_nx

  return ([NonLinear t u], flags_cons)

-- Box typing rule
{-
     G |- t : !1 (T -> U)  [L]
   -----------------------------------------------  (box 1)
     G |- box[T] t : T'  [L u {T' <: circ (T, U)]
-}
constraint_typing typctx (EApp (EBox a) t) typ = do
  b <- new_type
  -- Type the term t
  (lcons, fcons) <- constraint_typing typctx t (TExp 0 (TArrow a b))
  
  return ((NonLinear (TExp (-1) (TCirc a b)) typ):lcons, fcons)

-- rev typing rule
{-
         G |- t : Circ (T, U)  [L]
       --------------------------------
         G |- rev t : Circ (U, T)  [L]
-}
constraint_typing typctx (EApp ERev t) typ = do
  a <- new_type
  b <- new_type
  -- Type t
  (lcons, fcons) <- constraint_typing typctx t (TExp (-1) (TCirc a b))

  return ((NonLinear (TExp (-1) (TCirc b a)) typ):lcons, fcons)


-- App typing rule
{-
     G1, !ID |- t : a -> T  [L]      G2, !ID |- u : a  [L']
   -----------------------------------------------------------
         G1, G2, !ID |- t u : T  [L u L' u {1 <= I}]
-}

constraint_typing typctx (EApp t u) b = do
  a <- new_type

  -- Extract the free variables of t and u
  fvt <- return $ free_var t
  fvu <- return $ free_var u

  -- Filter on the free variables of t and type t
  (typctx_fvt, _) <- sub_context fvt typctx
  (lcons, fcons) <- constraint_typing typctx_fvt t (TExp 0 (TArrow a b))

  -- Filter on the free variables of u and type u
  (typctx_fvu, _) <- sub_context fvu typctx
  (lcons', fcons') <- constraint_typing typctx_fvu u a

  -- Construction of the constraint for !I Delta (= ctx \\ fvt oplus fvu)
  (_, typctx_delta) <- sub_context ((fvt \\fvu) ++ (fvu \\ fvt)) typctx
  flags <- context_annotation typctx_delta
  flags_cons <- return $ List.map (\(_, f) -> (1, f)) flags
  
  return (lcons' ++ lcons, fcons' ++ fcons ++ flags_cons)

-- Lambda typing rule
{-
     !IG, x : a |- t : b  [L]
   ---------------------------------------------
     !IG |- \x.t : !n(a -> b)  [L u {n <= Ii}]
-}

constraint_typing typctx (EFun p e) t = do
  b <- new_type
  n <- fresh_flag

  -- Context annotations (without the pattern's bindings)
  flags <- context_annotation typctx

  -- Bind p in the current context
  (a, fca) <- create_pattern_type p
  typctx' <- bind_pattern p a typctx

  -- Type the expression e
  (lcons, fcons) <- constraint_typing typctx' e b

  -- Build the context constraints : n <= I
  flags_cons <- return $ List.map (\(_, f) -> (n, f)) flags

  return ((NonLinear (TExp n $ TArrow a b) t):lcons, fcons ++ flags_cons ++ fca)

-- Tensor intro typing rule
{-
     G1, !ID |- t : !n a  [L]           G2, !ID |- u : !n b  [L']
   ----------------------------------------------------------
     G1, G2, !ID |- <t, u> : T   [L u L' u {1 <= I} u {!n (a * b) <: T}]
-}

constraint_typing typctx (EPair t u) typ = do
  ta@(TExp n a) <- new_type
  tb@(TExp m b) <- new_type
  p <- fresh_flag

  -- Extract the free variables of t and u
  fvt <- return $ free_var t
  fvu <- return $ free_var u

  -- Filter on the free variables of t and type t
  (typctx_fvt, _) <- sub_context fvt typctx
  (lcons, fcons) <- constraint_typing typctx_fvt t ta

  -- Filter on the free variables of u and type u
  (typctx_fvu, _) <- sub_context fvu typctx
  (lcons', fcons') <- constraint_typing typctx_fvu u tb

  -- Construction of the constraints of delta, the intersection
  (_, typctx_delta) <- sub_context ((fvt \\ fvu) ++ (fvu \\ fvt)) typctx
  flags <- context_annotation typctx_delta
  flags_cons <- return $ List.map (\(_, f) -> (1, f)) flags
  
  return (lcons' ++ lcons ++ [NonLinear (TExp p $ TTensor ta tb) typ], (p, n):(p, m):(fcons' ++ fcons ++ flags_cons))


-- Tensor elim typing rule
{-
     G1, !ID |- t : !n<a, b>  [L]    G2, !ID, x : !na, y : !nb |- u : T  [L']
   -----------------------------------------------------------------------------
     G1, G2, !ID |- let <x, y> = t in u : T    [L u L' u {1 <= I}]
-}

constraint_typing typctx (ELet p t u) typ = do
  (a, fca) <- create_pattern_type p
  n <- fresh_flag

  -- Extract the free variables of t and u
  fvt <- return $ free_var t
  fvu <- return $ free_var u

  -- Filter on the free variables of t and type t
  (typctx_fvt, _) <- sub_context fvt typctx
  (lcons, fcons) <- constraint_typing typctx_fvt t a

  -- Filter on the free variables of u
  (typctx_fvu, _) <- sub_context fvu typctx
  -- Add x and y to the context
  typctx_fvu <- bind_pattern p a typctx_fvu
  -- Type u
  (lcons', fcons') <- constraint_typing typctx_fvu u typ
  
  -- Generate the flag constraints for the intersection
  (_, typctx_delta) <- sub_context ((fvt \\ fvu) ++ (fvu \\ fvt)) typctx
  flags <- context_annotation typctx_delta
  flags_cons <- return $ List.map (\(_, f) -> (1, f)) flags
  
  return (lcons' ++ lcons, fcons' ++ fcons ++ flags_cons ++ fca)

-- Typing rule (if)
{-
     G1, !ID |- e : bool [L]
     G2, !ID |- f : T    [L']              G2, !ID |- g : T  [L'']
   --------------------------------------------------------------------------------------------
     G1, G2, !ID |- if e then f else g : T   [L u L' u L'' u {1 <= I}]
-}

constraint_typing typctx (EIf e f g) typ = do
  -- Extract the free variables of e, f and g
  fve <- return $ free_var e
  fvfg <- return $ List.union (free_var f) (free_var g)
  
  -- Filter on the free variables of e and type e
  (typctx_fve, _) <- sub_context fve typctx
  (lcons, fcons) <- constraint_typing typctx_fve e (TExp 0 TBool)

  -- Filter on the free variables of f an g
  (typctx_fvfg, _) <- sub_context fvfg typctx

  -- Type f and g
  (lconsf, fconsf) <- constraint_typing typctx_fvfg f typ
  (lconsg, fconsg) <- constraint_typing typctx_fvfg g typ

  -- Generate the flag constraints for the intersection
  (_, typctx_delta) <- sub_context ((fve \\ fvfg) ++ (fvfg \\ fve)) typctx
  flags <- context_annotation typctx_delta
  flags_cons <- return $ List.map (\(_, f) -> (1, f)) flags
  
  return (lconsf ++ lconsg ++ lcons, fconsf ++ fconsg ++ fcons ++ flags_cons)

-- Unbox typing rule
{-
     G |- t : Circ (T, U)  [L]
   ----------------------------------
     G |- unbox t : !n (T -> U)  [L]
-}

constraint_typing typctx (EUnbox t) typ = do
  a <- new_type
  b <- new_type
  n <- fresh_flag
  -- Type t
  (lcons, fcons) <- constraint_typing typctx t (TExp 1 (TCirc a b))
  -- Return
  return ((NonLinear (TExp n (TArrow a b)) typ):lcons, fcons)

--------------------------------------------------------------------------
--------------------------------------------------------------------------

-- Break composite constrainst of the form :
  -- T -> U <: T' -> U'
  -- ! T <: ! U

break_composite :: ConstraintSet -> State ConstraintSet

-- Nothing to do
break_composite ([], lc) = return ([], lc)

-- Detailed constraints
break_composite ((Linear (TDetailed t det) u):lc, fc) = do
  case det of
    TypeOfE e -> do
        set_expr e
    _ -> do
        return ()
  break_composite ((Linear t u):lc, fc)

break_composite ((Linear t (TDetailed u det)):lc, fc) = do
  case det of
    TypeOfE e -> do
        set_expr e
    _ -> do
        return ()  
  break_composite ((Linear t u):lc, fc)

break_composite ((Linear TUnit TUnit):lc, fc) = do
  break_composite (lc, fc)

break_composite ((Linear TBool TBool):lc, fc) = do
  break_composite (lc, fc)

break_composite ((Linear TQbit TQbit):lc, fc) = do
  break_composite (lc, fc)

-- Break constraints
  -- T -> U <: T' -> U' 
-- Into
  -- T' <: T && U <: U'
break_composite ((Linear (TArrow t u) (TArrow t' u')):lc, fc) = do
  break_composite ((NonLinear t' t):(NonLinear u u'):lc, fc)

-- Break constraints
  -- T * U <: T' * U'
-- Into
  -- T <: T' && U <: U'

break_composite ((Linear (TTensor t u) (TTensor t' u')):lc, fc) = do
  break_composite ((NonLinear t t'):(NonLinear u u'):lc, fc)

-- Break constraints
  -- circ (T, U) <: circ (T', U')
-- Into
  -- T' <: T && U <: U'
break_composite ((Linear (TCirc t u) (TCirc t' u')):lc, fc) = do
  break_composite ((NonLinear t' t):(NonLinear u u'):lc, fc)

-- Break constraints
  -- !n T <: !m U
-- Into
  -- T <: U && m <= n
break_composite ((NonLinear (TExp n TQbit) (TExp m u)):lc, fc) = do
  break_composite ((Linear TQbit u):lc, (m, 0):fc)

break_composite ((NonLinear (TExp n t) (TExp m TQbit)):lc, fc) = do
  break_composite ((Linear t TQbit):lc, (n, 0):fc)

break_composite ((NonLinear (TExp n t) (TExp m u)):lc, fc) = do
  break_composite ((Linear t u):lc, (m, n):fc)

-- Semi composite (unbreakable) constraints
break_composite (c@(Linear (TVar _) _):lc, fc) = do
  (lc', fc') <- break_composite (lc, fc)
  return (c:lc', fc')

break_composite (c@(Linear _ (TVar _)):lc, fc) = do
  (lc', fc') <- break_composite (lc, fc)
  return (c:lc', fc')

-- Other non composite / non-semi composite constraints
break_composite ((Linear t u):lc, fc) = do
  e <- get_expr
  fail $ "Type mismacth in the type of " ++ pprint e
  --failwith $ TypeMismatch (pprint t) (pprint u)

-------------------------------------- UNIFICATION -----------------------------------------------------

-- Instanciation of model types
  -- The bang annotations of the model are ignored
model_of_lin :: LinType -> State LinType
model_of :: Type -> State Type
map_to_model :: Variable -> LinType -> State LinType
-------------------------------------------------------------------------
model_of_lin TUnit = do
  return TUnit

model_of_lin TBool = do
  return TBool

model_of_lin TQbit = do
  return TQbit

model_of_lin (TArrow t u) = do
  t' <- model_of t
  u' <- model_of u
  return $ TArrow t' u'

model_of_lin (TTensor t u) = do
  t' <- model_of t
  u' <- model_of u
  return $ TTensor t' u'

model_of_lin (TVar _) = do
  x <- fresh_type
  -- Add the variable to the list managed by the ordering process
  add_variable x
  return $ TVar x

model_of_lin (TCirc t u) = do
  t' <- model_of t
  u' <- model_of u
  return $ TCirc t' u'

model_of (TExp _ t) = do
  n <- fresh_flag
  t' <- model_of_lin t
  return $ TExp n t'

-------------
map_to_model x t = do
  t' <- model_of_lin t
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
                                                          Linear (TVar x) _ -> List.elem x cx
                                                          Linear _ (TVar y) -> List.elem y cx) lc
        
      -- Log
      logx <- return $ List.foldl (\s c -> "(" ++ pprint c ++ ") " ++ s) "" lcx
      lognonx <- return $ List.foldl (\s c -> "(" ++ pprint c ++ ") " ++ s) "" non_lcx
      new_log logx
      new_log lognonx
                                             
      -- Filter the atomic constraints
      (atomx, natomx) <- return $ List.partition is_atomic lcx

      -- Check the next action
      case (atomx, natomx) of

        -- No semi-composite constraints : trivial solution with x1 = .. = xn,  unify the rest
        (atomx, []) -> do
            (non_lcx', fc') <- unify (non_lcx, fc)
            return (non_lcx' ++ atomx, fc')

        -- Semi-composite constraints :
           -- Pick up a sample type, and map all variables of cx to an instance of this type
        (atomx, cset) -> do
            
            -- If all the constraints are chained as : T <: x1 <: .. <: xn <: U, make the approximation x1 = .. = xn = T
            (ischain, sorted) <- return $ chain_constraints lcx
            
            if ischain then do
              new_log "CHAINED"
              leftend <- case List.head sorted of
                           Linear t _ -> return $ t
              rightend <- case List.last sorted of
                            Linear _ t -> return t

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

                    (cset', fc') <- break_composite ([Linear leftend rightend], fc)
                    register_constraints cset'
                    -- Unify the rest
                    unify (cset' ++ non_lcx, fc')

            else do           
              new_log "UNCHAINED"
              
              onesided <- return $ is_one_sided cset
              -- If all the constraints are one-sided, make the approximation : x1 = .. = xn
              cset <- if onesided then do
                      new_log "ONE SIDED"
                      cxh <- return $ List.head cx
                      List.foldl (\rec x -> do
                                      rec
                                      mapsto x $ TVar cxh) (return ()) $ List.tail cx
                      return $ List.map (\c -> case c of
                                                 Linear (TVar _) t -> Linear (TVar cxh) t
                                                 Linear t (TVar _) -> Linear t (TVar cxh)) cset
                    else do
                      return cset


              model <- return $ constraint_unifier cset

              new_log $ pprint model

            
              List.foldl (\rec x -> do
                             rec
                             _ <- map_to_model x model
                             return ()) (return ()) cx
            
              -- Rewrite and reduce the atomic constraints
              atomx' <- List.foldl (\rec (Linear (TVar x) (TVar y)) -> do
                                      (lr, fr) <- rec
                                      xt <- appmap x
                                      yt <- appmap y
                                      (lr', fr')  <- break_composite ([Linear xt yt], fr)
                                      return (lr' ++ lr, fr')) (return (non_lcx, fc)) atomx

              -- Rewrite and reduce the remaining constraints
              (cset', fc'') <- List.foldl (\rec c -> do
                                     (lr, fr) <- rec
                                     c' <- case c of
                                             Linear (TVar x) t -> do
                                                 xt <- appmap x
                                                 return $ Linear xt t
                                             Linear t (TVar x) -> do
                                                 xt <- appmap x
                                                 return $ Linear t xt
                                     (lr', fr') <- break_composite ([c'], fr)
                                     return (lr' ++ lr, fr')) (return atomx') cset
              
              -- Register the new relations defined by those constraints
              register_constraints cset'

              -- Unifcation of the remaining
              unify (cset', fc'')

-- Flag unification

-- Set a flag value
set_flag :: Int -> Int -> Map.Map Int Int -> State (Map.Map Int Int)
-----------------------------------------------------------------------
set_flag f n val = do
  case Map.lookup f val of
    Just m | m == n -> do return val
           | otherwise -> do fail ("Unsolvable flag constraint set : flag " ++ show f)
    _ -> do return $ Map.insert f n val 


apply_constraints :: [FlagConstraint] -> Map.Map Int Int -> State (Bool, [FlagConstraint], Map.Map Int Int)
-----------------------------------------------------------------------------------------------------------
apply_constraints [] v = do
  return (False, [], v)

apply_constraints (c:cc) v = do
  case c of
    (1, 0) -> do
        fail "Absurd constraint 1 <= 0"

    (n, 0) -> do
        v' <- set_flag n 0 v
        (_, cc', v'') <- apply_constraints cc v'
        return (True, cc', v'')

    (1, m) -> do
        v' <- set_flag m 1 v
        (_, cc', v'') <- apply_constraints cc v'
        return (True, cc', v'')

    (m, n) -> do
      case (Map.lookup m v, Map.lookup n v) of
        (Nothing, Nothing) -> do
            (b, cc', v') <- apply_constraints cc v
            return (b, c:cc', v')

        (Just 1, Just 0) -> do
            fail "Absurd constraint 1 <= 0"

        (Nothing, Just 0) -> do
            v' <- set_flag m 0 v
            (_, cc', v'') <- apply_constraints cc v'
            return (True, cc', v'')

        (Just 1, Nothing) -> do
            v' <- set_flag n 1 v
            (_, cc', v'') <- apply_constraints cc v'
            return (True, cc', v'')

        _ -> do
            apply_constraints cc v

solve_constraints :: [FlagConstraint] -> Map.Map Int Int -> State ([FlagConstraint], Map.Map Int Int)
-----------------------------------------------------------------------------------------------------
solve_constraints fc v = do
  (b, fc', v') <- apply_constraints fc v
  if b then
    solve_constraints fc' v'
  else
    return (fc', v')

-- Solve the constraint set
solve_annotation :: [FlagConstraint] -> State (Map.Map Int Int)
----------------------------------------------------------------
solve_annotation fc = do
  -- Empty valuation
  valuation <- return $ Map.empty

  -- Elimination of trivial constraints f <= 1 and 0 <= f, -1 <= f and f <= -1
  fc' <- return $ List.filter (\(m, n) -> m /= 0 && n /= 1 && m /= -1 && n /= -1) fc

  -- Application of the constraints 1 <= f and f <= 0
  (fc'', val) <- solve_constraints fc' valuation

  return val

