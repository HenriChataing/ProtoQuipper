module TypeInference where

import Classes
import Utils
import Localizing
import QuipperError

import CoreSyntax

import QpState
import TypingContext

import Subtyping
import Ordering

import Control.Exception as E

import Data.List as List
import Data.Sequence as Seq
import Data.Array as Array
import qualified Data.Map as Map
import qualified Data.Set as Set


-- Build all the deriving constraints
constraint_typing :: TypingContext -> Expr -> Type -> QpState ConstraintSet


-- | Located things
-- Change the location and resume

constraint_typing typctx (ELocated e ex) t = do
  set_location ex
  constraint_typing typctx e t


-- | Unit typing rule
--
-- -------------------
--  !I G  |- * : !n T  [{1 <= I}]
--

constraint_typing typctx EUnit t = do
  flags <- context_annotation typctx
  flags_cons <- return $ List.map (\(_, f) -> (1, f)) flags

  -- Detailed information
  ex <- get_location
  detail <- return $ ActualOfE EUnit ex

  return ([NonLinear t (TExp 1 (TUnit, detail))], flags_cons)


-- | True / False typing rule
--
-- --------------------------------
--  !I G |- True / False : !n bool  [{1 <= I}]
-- 

constraint_typing typctx (EBool b) t = do
  flags <- context_annotation typctx
  flags_cons <- return $ List.map (\(_, f) -> (1, f)) flags

  -- Detailed information
  ex <- get_location
  detail <- return $ ActualOfE (EBool b) ex

  return ([NonLinear t (TExp 1 (TBool, detail))], flags_cons)


-- | Axiom typing rule
--
-- ---------------------
--  !IG, t : T |- t : U  [{T <: U, 1 <= I}]
--

constraint_typing typctx (EVar x) u = do
  t <- type_of x typctx
  flags <- context_annotation typctx
  flags_nx <- return $ List.deleteBy (\(x, _) (y, _) -> x == y) (x, 0) flags
  flags_cons <- return $ List.map (\(_, f) -> (1, f)) flags_nx

  return ([NonLinear t u], flags_cons)


-- | Box typing rule
--
-- ---------------------------------------------------
--   G |- box[T] : !1 (!1 (T -> U) -> !1 Circ (T, U))  [L u {T' <: circ (T, U)]
--

constraint_typing typctx (EBox a) typ = do
  b <- new_type

  ex <- get_location
 
  flags <- context_annotation typctx
  flags_cons <- return $ List.map (\(_, f) -> (1, f)) flags

  arw <- return $ TExp 1 (TArrow a b, NoInfo)
  cir <- return $ TExp 1 (TCirc a b, NoInfo)

  detail <- return $ ActualOfE (EBox a) ex

  return ([NonLinear (TExp 1 (TArrow arw cir, detail)) typ], flags_cons)
  

-- | Rev typing rule
--
-- --------------------------------------------
--  G |- rev : !1 (Circ (T, U) -> Circ (U, T))  [L]
--

constraint_typing typctx ERev typ = do
  a <- new_type
  b <- new_type

  ex <- get_location

  flags <- context_annotation typctx
  flags_cons <- return $ List.map (\(_, f) -> (1, f)) flags

  cirab <- return $ TExp 1 (TCirc a b, NoInfo)
  cirba <- return $ TExp 1 (TCirc b a, NoInfo) 

  detail <- return $ ActualOfE ERev ex

  return ([NonLinear (TExp 1 (TArrow cirab cirba, detail)) typ], flags_cons)


-- App typing rule
--
--  G1, !ID |- t : a -> T   [L] 
--     G2, !ID |- u : a     [L']
-- ------------------------
--  G1, G2, !ID |- t u : T  [L u L' u {1 <= I}]
--

constraint_typing typctx (EApp t u) b = do
  a <- new_type

  -- Extract the free variables of t and u
  fvt <- return $ free_var t
  fvu <- return $ free_var u

  -- Filter on the free variables of t and type t
  (typctx_fvt, _) <- sub_context fvt typctx
  (lcons, fcons) <- constraint_typing typctx_fvt t (TExp 0 (TArrow a b, NoInfo))

  -- Filter on the free variables of u and type u
  (typctx_fvu, _) <- sub_context fvu typctx
  (lcons', fcons') <- constraint_typing typctx_fvu u a

  -- Construction of the constraint for !I Delta (= ctx \\ fvt oplus fvu)
  (_, typctx_delta) <- sub_context ((fvt \\fvu) ++ (fvu \\ fvt)) typctx
  flags <- context_annotation typctx_delta
  flags_cons <- return $ List.map (\(_, f) -> (1, f)) flags
  
  return (lcons' ++ lcons, fcons' ++ fcons ++ flags_cons)


-- Lambda typing rule
--
--    !IG, x : a |- t : b     [L]
-- --------------------------
--  !IG |- \x.t : !n(a -> b)  [L u {n <= Ii}]
--

constraint_typing typctx (EFun p e) t = do
  b <- new_type
  n <- fresh_flag
 
  ex <- get_location

  -- Context annotations (without the pattern's bindings)
  flags <- context_annotation typctx

  -- Bind p in the current context
  (a, typctx', (lca, fca)) <- bind_pattern p typctx

  -- Type the expression e
  (lcons, fcons) <- constraint_typing typctx' e b

  -- Build the context constraints : n <= I
  flags_cons <- return $ List.map (\(_, f) -> (n, f)) flags

  detail <- return $ ActualOfE (EFun p e) ex

  return ((NonLinear (TExp n (TArrow a b, detail)) t):(lcons ++ lca), fcons ++ flags_cons ++ fca)


-- Tensor intro typing rule
--
--    G1, !ID |- t : !n a      [L]
--    G2, !ID |- u : !n b      [L']
-- ---------------------------
--  G1, G2, !ID |- <t, u> : T  [L u L' u {1 <= I} u {!n (a * b) <: T}]
--

constraint_typing typctx (ETuple elist) typ = do
  -- Create n new types
  tlist <- List.foldr (\_ rec -> do
                         r <- rec
                         t <- new_type
                         return (t:r)) (return []) elist

  -- And the flag of the tensor
  p <- fresh_flag

  -- Get the extent of the tuple before starting moving into the inner expressions
  ex <- get_location

  -- Extract the free variables of all the inner expressions
  fvlist <- List.foldr (\e rec -> do
                          r <- rec
                          fv <- return $ free_var e
                          return (fv:r)) (return []) elist

  -- Type the inner expressions, and extract the constraints
  (lincons, fcons) <- List.foldr (\(e, t, fv) rec -> do
                                    (fc, lc) <- rec
                                    (typctx_fv, _) <- sub_context fv typctx
                                    (fc', lc') <- constraint_typing typctx_fv e t
                                    return (fc' ++ fc, lc' ++ lc)) (return ([], [])) (List.zip3 elist tlist fvlist)

  -- Construction of all the constraints p <= f1 ... p <= fn
  pcons <- return $ List.map (\(TExp n _) -> (p, n)) tlist

  -- Disjoint union of all the free variables
  disunion <- List.foldl (\rec fv -> do
                            r <- rec
                            return $ (r \\ fv) ++ (fv \\ r)) (return []) fvlist

  -- Construction of the constraints of delta, the intersection
  (_, typctx_delta) <- sub_context disunion typctx
  flags <- context_annotation typctx_delta
  flags_cons <- return $ List.map (\(_, f) -> (1, f)) flags
  
  detail <- return $ ActualOfE (ETuple elist) ex

  return (lincons ++ [NonLinear (TExp p (TTensor tlist, detail)) typ], pcons ++ fcons ++ flags_cons)


-- Tensor elim typing rule
--
--     G1, !ID |- t : !n<a, b>  [L]    G2, !ID, x : !na, y : !nb |- u : T  [L']
--   -----------------------------------------------------------------------------
--     G1, G2, !ID |- let <x, y> = t in u : T    [L u L' u {1 <= I}]
--

constraint_typing typctx (ELet p t u) typ = do
  -- Extract the free variables of t and u
  fvt <- return $ free_var t
  fvu <- return $ free_var u

  -- Give the corresponding sub contexts
  (typctx_fvt, _) <- sub_context fvt typctx
  (typctx_fvu, _) <- sub_context fvu typctx

  -- Create the type of the pattern
  (a, typctx_fvu', (lca, fca)) <- bind_pattern p typctx_fvu

  -- Type t with this type
  (lcons, fcons) <- constraint_typing typctx_fvt t a 
  
  -- Type u
  (lcons', fcons') <- constraint_typing typctx_fvu' u typ
  
  -- Generate the flag constraints for the intersection
  (_, typctx_delta) <- sub_context ((fvt \\ fvu) ++ (fvu \\ fvt)) typctx
  flags <- context_annotation typctx_delta
  flags_cons <- return $ List.map (\(_, f) -> (1, f)) flags
  
  return (lcons' ++ lcons ++ lca, fcons' ++ fcons ++ flags_cons ++ fca)


-- Data typing rule
--
-- Supposing the type definition
--   type UserT =
--       ..
--     | datacon !n A
--       ..
--
--
--      G |- t : !n A      [L]
-- -----------------------
--  G |- datacon t : !p UserT  [L u {p <= n}]
--

constraint_typing typctx (EData dcon t) typ = do
  ex <- get_location
  p <- fresh_flag
  (typename, dtype@(TExp n _)) <- datacon_def dcon

  -- The term t must have the type required as argument of the data constructor dcon
  (lcons, fcons) <- constraint_typing typctx t dtype

  detail <- return $ ActualOfE (EData dcon t) ex
  return ((NonLinear (TExp p (TUser typename, detail)) typ):lcons, (p, n):fcons)


-- Match typing rule
--
--          G1, !ID |- t : !p(!nA + !m B)              [L1]
--            G2, !ID, x : !nA |- u : V                [L2]
--            G2, !ID, y : !mB |- v : V                [L3]
-- ---------------------------------------------------
--  G1, G2, !ID |- match t with (x -> u | y -> v) : V  [L1 u L2 u L3 u {1 <= I, p <= n, p <= m}]
--

constraint_typing typctx (EMatch e blist) typ = do
  ex <- get_location
 
  fve <- return $ free_var e
  fvlist <- List.foldl (\rec (p, f) -> do
                          r <- rec
                          fv <- return $ free_var f \\ free_var p
                          return $ List.union fv r) (return []) blist
  
  -- Create the type of the expression e, and type e
  a <- new_type
  (typctx_fve, _) <- sub_context fve typctx
  (lincons, fcons) <- constraint_typing typctx_fve e a

  -- Type each of the bindings
  (typctx_fvlist, _) <- sub_context fvlist typctx
  (lincons', fcons') <- List.foldl (\rec (p, f) -> do
                                      (lc, fc) <- rec
                                      (b, typctx_fvlist', (lcb, fcb)) <- bind_pattern p typctx_fvlist

                                      (lc', fc') <- constraint_typing typctx_fvlist' f typ
                                      return ((NonLinear b a):(lc' ++ lc ++ lcb), fc' ++ fc ++ fcb)) (return (lincons, fcons)) blist

  -- Generate the flag constraints for the intersection
  disunion <- return $ (fve \\ fvlist) ++ (fvlist \\ fve)
  (_, typctx_delta) <- sub_context disunion typctx
  flags <- context_annotation typctx_delta
  flags_cons <- return $ List.map (\(_, f) -> (1, f)) flags
  
  return (lincons', fcons' ++ flags_cons) 


-- Typing rule (if)
--
--     G1, !ID |- e : bool                 [L]
--       G2, !ID |- f : T                  [L']
--       G2, !ID |- g : T                  [L'']
-- ---------------------------------------
--  G1, G2, !ID |- if e then f else g : T  [L u L' u L'' u {1 <= I}]
--

constraint_typing typctx (EIf e f g) typ = do
  -- Extract the free variables of e, f and g
  fve <- return $ free_var e
  fvfg <- return $ List.union (free_var f) (free_var g)
  
  -- Filter on the free variables of e and type e
  (typctx_fve, _) <- sub_context fve typctx
  (lcons, fcons) <- constraint_typing typctx_fve e (TExp 0 (TBool, NoInfo))

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
--    
-- ------------------------------------------------
--  G |- unbox : !1 (!1 circ(T, U) -> !1 (T -> U))  [L]
--

constraint_typing typctx EUnbox typ = do
  a <- new_type
  b <- new_type
  n <- fresh_flag
  arw <- return $ TExp n (TArrow a b, NoInfo)
  cir <- return $ TExp (-1) (TCirc a b, NoInfo)

  ex <- get_location
  detail <- return $ ActualOfE EUnbox ex

  -- Return
  return ([NonLinear (TExp (-1) (TArrow cir arw, detail)) typ], [])

--------------------------------------------------------------------------
--------------------------------------------------------------------------

-- Break composite constrainst of the form :
  -- T -> U <: T' -> U'
  -- ! T <: ! U

break_composite :: ConstraintSet -> QpState ConstraintSet

-- Nothing to do
break_composite ([], lc) = return ([], lc)

break_composite ((Linear (TLocated t _, _) u):lc, fc) = do
  break_composite ((Linear t u):lc, fc)

break_composite ((Linear t (TLocated u _, _)):lc, fc) = do
  break_composite ((Linear t u):lc, fc)

break_composite ((Linear (TUnit, _) (TUnit, _)):lc, fc) = do
  break_composite (lc, fc)

break_composite ((Linear (TBool, _) (TBool, _)):lc, fc) = do
  break_composite (lc, fc)

break_composite ((Linear (TQbit, _) (TQbit, _)):lc, fc) = do
  break_composite (lc, fc)

-- Break constraints
  -- T -> U <: T' -> U' 
-- Into
  -- T' <: T && U <: U'
break_composite ((Linear (TArrow t u, d) (TArrow t' u', d')):lc, fc) = do
  dt <- return $ add_detail d t
  du <- return $ add_detail d u
  dt' <- return $ add_detail d' t'
  du' <- return $ add_detail d' u'
  break_composite ((NonLinear dt' dt):(NonLinear du du'):lc, fc)

-- Break constraints
  -- T * U <: T' * U'
-- Into
  -- T <: T' && U <: U'

break_composite ((Linear (TTensor tlist, d) (TTensor tlist', d')):lc, fc) = do
  case (tlist, tlist') of
    ([], []) ->
        break_composite (lc, fc)

    (t:rest, t':rest') -> do
        dt <- return $ add_detail d t
        dt' <- return $ add_detail d' t'
        break_composite ((Linear (TTensor rest, d) (TTensor rest', d')):(NonLinear dt dt'):lc, fc)

    _ ->
        throw $ TypingError (pprint (TTensor tlist, d)) (pprint (TTensor tlist', d'))

-- Break constraints
  -- T + U <: T' + U'
-- Into
  -- T <: T' && U <: U'

break_composite ((Linear (TUser n, d) (TUser m, d')):lc, fc) = do
  if n == m then do
    break_composite (lc, fc)
  else
    throw $ TypingError (pprint (TUser n, d)) (pprint (TUser m, d'))


-- Break constraints
  -- circ (T, U) <: circ (T', U')
-- Into
  -- T' <: T && U <: U'
break_composite ((Linear (TCirc t u, d) (TCirc t' u', d')):lc, fc) = do
  dt <- return $ add_detail d t
  du <- return $ add_detail d u
  dt' <- return $ add_detail d' t'
  du' <- return $ add_detail d' u'
  break_composite ((NonLinear dt' dt):(NonLinear du du'):lc, fc)

-- Break constraints
  -- !n T <: !m U
-- Into
  -- T <: U && m <= n
break_composite ((NonLinear (TExp n (TQbit, d)) (TExp m u)):lc, fc) = do
  break_composite ((Linear (TQbit, d) u):lc, (m, 0):fc)

break_composite ((NonLinear (TExp n t) (TExp m (TQbit, d))):lc, fc) = do
  break_composite ((Linear t (TQbit, d)):lc, (n, 0):fc)

break_composite ((NonLinear (TExp n t) (TExp m u)):lc, fc) = do
  break_composite ((Linear t u):lc, (m, n):fc)

-- Semi composite (unbreakable) constraints
break_composite (c@(Linear (TVar _, _) _):lc, fc) = do
  (lc', fc') <- break_composite (lc, fc)
  return (c:lc', fc')

break_composite (c@(Linear _ (TVar _, _)):lc, fc) = do
  (lc', fc') <- break_composite (lc, fc)
  return (c:lc', fc')

-- Other non composite / non-semi composite constraints
break_composite ((Linear t@(_, d) u@(_, d')):lc, fc) = do
  case (d, d') of
    (ActualOfE e ex, _) -> throwQ $ DetailedTypingError (pprint t) (pprint u) (sprint e) ex
    (_, ActualOfE e ex) -> throwQ $ DetailedTypingError (pprint u) (pprint t) (sprint e) ex
    (ActualOfP p ex, _) -> throwQ $ DetailedTypingError (pprint t) (pprint u) (sprint p) ex
    (_, ActualOfP p ex) -> throwQ $ DetailedTypingError (pprint u) (pprint t) (sprint p) ex
    _ -> throwQ $ TypingError (pprint t) (pprint u) 

-------------------------------------- UNIFICATION -----------------------------------------------------

-- Instanciation of model types
  -- The bang annotations of the model are ignored
model_of_lin :: LinType -> QpState LinType
model_of :: Type -> QpState Type
map_to_model :: Variable -> LinType -> QpState LinType
-------------------------------------------------------------------------
model_of_lin (TUnit, _) = do
  return (TUnit, NoInfo)

model_of_lin (TBool, _) = do
  return (TBool, NoInfo)

model_of_lin (TQbit, _) = do
  return (TQbit, NoInfo)

model_of_lin (TArrow t u, _) = do
  t' <- model_of t
  u' <- model_of u
  return (TArrow t' u', NoInfo)

model_of_lin (TTensor tlist, _) = do
  tlist' <- List.foldr (\t rec -> do
                          r <- rec
                          t' <- model_of t
                          return (t':r)) (return []) tlist
  return (TTensor tlist', NoInfo)

model_of_lin (TUser n, _) = do
  return (TUser n, NoInfo)

model_of_lin (TVar _, _) = do
  x <- fresh_type
  -- Add the variable to the list managed by the ordering process
  add_variable x
  return (TVar x, NoInfo)

model_of_lin (TCirc t u, _) = do
  t' <- model_of t
  u' <- model_of u
  return (TCirc t' u', NoInfo)

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

unify :: ConstraintSet -> QpState ConstraintSet
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
                                                          Linear (TVar x, _) _ -> List.elem x cx
                                                          Linear _ (TVar y, _) -> List.elem y cx) lc
        
      -- Log
      logx <- return $ List.foldl (\s c -> "(" ++ pprint c ++ ") " ++ s) "" lcx
      lognonx <- return $ List.foldl (\s c -> "(" ++ pprint c ++ ") " ++ s) "" non_lcx
      newlog 0 logx
      newlog 0 lognonx
                                             
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
              newlog 0 "CHAINED"
              leftend <- case List.head sorted of
                           Linear t _ -> return $ t
              rightend <- case List.last sorted of
                            Linear _ t -> return t

              -- Map x1 .. xn to T or U
              case (leftend, rightend) of
                ((TVar x, _), _) -> do
                    List.foldl (\rec x -> do
                                  rec
                                  mapsto x rightend) (return ()) cx
                    -- Unify the rest
                    unify (non_lcx, fc)
                    
                (_, (TVar x, _)) -> do
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
              newlog 0 "UNCHAINED"
              
              onesided <- return $ is_one_sided cset
              -- If all the constraints are one-sided, make the approximation : x1 = .. = xn
              cset <- if onesided then do
                      newlog 0 "ONE SIDED"
                      cxh <- return $ List.head cx
                      List.foldl (\rec x -> do
                                      rec
                                      mapsto x (TVar cxh, NoInfo)) (return ()) $ List.tail cx
                      return $ List.map (\c -> case c of
                                                 Linear (TVar _, _) t -> Linear (TVar cxh, NoInfo) t
                                                 Linear t (TVar _, _) -> Linear t (TVar cxh, NoInfo)) cset
                    else do
                      return cset


              model <- return $ constraint_unifier cset

              newlog 0 $ pprint model

            
              List.foldl (\rec x -> do
                             rec
                             _ <- map_to_model x model
                             return ()) (return ()) cx
            
              -- Rewrite and reduce the atomic constraints
              atomx' <- List.foldl (\rec (Linear (TVar x, _) (TVar y, _)) -> do
                                      (lr, fr) <- rec
                                      xt <- appmap x
                                      yt <- appmap y
                                      (lr', fr')  <- break_composite ([Linear xt yt], fr)
                                      return (lr' ++ lr, fr')) (return (non_lcx, fc)) atomx

              -- Rewrite and reduce the remaining constraints
              (cset', fc'') <- List.foldl (\rec c -> do
                                     (lr, fr) <- rec
                                     c' <- case c of
                                             Linear (TVar x, _) t -> do
                                                 xt <- appmap x
                                                 return $ Linear xt t
                                             Linear t (TVar x, _) -> do
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
set_flag :: Int -> Int -> Map.Map Int Int -> QpState (Map.Map Int Int)
-----------------------------------------------------------------------
set_flag f n val = do
  case Map.lookup f val of
    Just m | m == n -> do return val
           | otherwise -> do fail ("Unsolvable flag constraint set : flag " ++ show f)
    _ -> do return $ Map.insert f n val 


apply_constraints :: [FlagConstraint] -> Map.Map Int Int -> QpState (Bool, [FlagConstraint], Map.Map Int Int)
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

solve_constraints :: [FlagConstraint] -> Map.Map Int Int -> QpState ([FlagConstraint], Map.Map Int Int)
-----------------------------------------------------------------------------------------------------
solve_constraints fc v = do
  (b, fc', v') <- apply_constraints fc v
  if b then
    solve_constraints fc' v'
  else
    return (fc', v')

-- Solve the constraint set
solve_annotation :: [FlagConstraint] -> QpState (Map.Map Int Int)
----------------------------------------------------------------
solve_annotation fc = do
  -- Empty valuation
  valuation <- return $ Map.empty

  -- Elimination of trivial constraints f <= 1 and 0 <= f, -1 <= f and f <= -1
  fc' <- return $ List.filter (\(m, n) -> m /= 0 && n /= 1 && m /= -1 && n /= -1) fc

  -- Application of the constraints 1 <= f and f <= 0
  (fc'', val) <- solve_constraints fc' valuation

  return val

