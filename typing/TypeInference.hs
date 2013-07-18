module TypeInference where

import Classes
import Utils
import Localizing
import QuipperError

import Syntax (RecFlag (..))
import CoreSyntax

import QpState
import TypingContext

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
  -- The context must be duplicable
  fconstraints <- have_duplicable_context typctx
  
  -- Generates a referenced flag of the actual type of EUnit
  ex <- get_location
  n <- fresh_flag_with_value Any
  specify_expression n $ ActualOfE EUnit
  specify_location n ex

  return ([TBang n TUnit <: t], fconstraints)


-- | True / False typing rule
--
-- --------------------------------
--  !I G |- True / False : !n bool  [{1 <= I}]
-- 

constraint_typing typctx (EBool b) t = do
  -- The context must be duplicable
  fconstraints <- have_duplicable_context typctx

  -- Generates a referenced flag of the actual type of EBool
  ex <- get_location
  n <- fresh_flag_with_value Any
  specify_expression n $ ActualOfE (EBool b)
  specify_location n ex

  return ([TBang n TBool <: t], fconstraints)


-- | Axiom typing rule
--
-- ---------------------
--  !IG, t : T |- t : U  [{T <: U, 1 <= I}]
--

constraint_typing typctx (EVar x) u = do
  -- Retrieve the type of x from the typing context
  t <- type_of x typctx
  (t, cset) <- instanciate t -- In case t is a typing scheme

  -- Have the rest of the context be duplicable
  flags <- context_annotation typctx
  flags_nx <- return $ List.deleteBy (\(x, _) (y, _) -> x == y) (x, 0) flags
  fconstraints <- return $ List.map (\(_, f) -> (one, f)) flags_nx

  return $ ([t <: u], fconstraints) <> cset


-- | Box typing rule
--
-- ------------------------------------------------------
--  !I G |- box[T] :  !n (!1 (T -> U) -> !n Circ (T, U))  [L u {1 <= I}]
--

constraint_typing typctx (EBox (TForall _ _ cset a)) typ = do
  -- The context must be duplicable 
  fconstraints <- have_duplicable_context typctx

  -- Flag reference
  ex <- get_location
  n <- fresh_flag_with_value Any
  specify_expression n $ ActualOfE (EBox a)
  specify_location n ex

  -- Build the type of box
  b <- new_type  
  arw <- return $ TBang one (TArrow a b)
  cir <- return $ TBang anyflag (TCirc a b)

  return $ cset <> ([TBang n (TArrow arw cir) <: typ], fconstraints)
  

-- | Rev typing rule
--
-- --------------------------------------------
--  G |- rev : !n (!n Circ (T, U) -> !n Circ (U, T))  [L]
--

constraint_typing typctx ERev typ = do
  -- The context must be duplicable
  fconstraints <- have_duplicable_context typctx

  -- Flag reference
  ex <- get_location
  n <- fresh_flag_with_value Any
  specify_expression n $ ActualOfE ERev
  specify_location n ex

  -- Build the type of rev
  a <- new_type
  b <- new_type
  cirab <- return $ TBang anyflag (TCirc a b)
  cirba <- return $ TBang anyflag (TCirc b a)

  return ([TBang n (TArrow cirab cirba) <: typ], fconstraints)


-- Unbox typing rule
--    
-- ------------------------------------------------
--  G |- unbox : !1 (!n circ(T, U) -> !1 (T -> U))  [L]
--

constraint_typing typctx EUnbox typ = do
  -- The context must be duplicable
  fconstraints <- have_duplicable_context typctx

  -- Flag reference
  ex <- get_location
  n <- fresh_flag_with_value Any
  specify_expression n $ ActualOfE EUnbox
  specify_location n ex

  -- Build the type of unbox
  a <- new_type
  b <- new_type
  arw <- return $ TBang one (TArrow a b)
  cir <- return $ TBang anyflag (TCirc a b)

  return ([(TBang n (TArrow cir arw)) <: typ], fconstraints)


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
  n <- fresh_flag
  csett <- constraint_typing typctx_fvt t (TBang n (TArrow a b))

  -- Filter on the free variables of u and type u
  (typctx_fvu, _) <- sub_context fvu typctx
  csetu <- constraint_typing typctx_fvu u a

  -- Construction of the constraint for !I Delta, the intersection of Gt and Gu
  disunion <- return $ disjoint_union [fvt, fvu]
  (_, typctx_delta) <- sub_context disunion typctx
  fconstraints <- have_duplicable_context typctx_delta
  
  return $ csett <> csetu <> ([], fconstraints)


-- Lambda typing rule
--
--    !IG, x : a |- t : b     [L]
-- --------------------------
--  !IG |- \x.t : !n(a -> b)  [L u {n <= Ii}]
--

constraint_typing typctx (EFun p e) t = do
  -- Detailed information 
  ex <- get_location
  n <- fresh_flag
  specify_expression n $ ActualOfE (EFun p e)
  specify_location n ex

  -- Context annotations (without the pattern's bindings)
  flags <- context_annotation typctx
  
  -- Bind p in the current context - this returns the type a of the argument of the abstraction
  (a, typctx', cseta) <- bind_pattern p typctx
  b <- new_type

  -- Type the expression e
  csete <- constraint_typing typctx' e b

  -- Build the context constraints : n <= I
  fconstraints <- return $ List.map (\(_, f) -> (n, f)) flags

  return $ cseta <> csete <> ([TBang n (TArrow a b) <: t], fconstraints)


-- Tensor intro typing rule
--
--    G1, !ID |- t : !n a      [L]
--    G2, !ID |- u : !n b      [L']
-- ---------------------------
--  G1, G2, !ID |- <t, u> : T  [L u L' u {1 <= I} u {!n (a * b) <: T}]
--

constraint_typing typctx (ETuple elist) typ = do
  -- Detailed information
  ex <- get_location
  p <- fresh_flag
  specify_expression p $ ActualOfE (ETuple elist)
  specify_location p ex  

  -- Create n new types
  tlist <- List.foldr (\_ rec -> do
                         r <- rec
                         t <- new_type
                         return (t:r)) (return []) elist

  -- And the flag of the tensor
  p <- fresh_flag

  -- Extract the free variables of all the inner expressions
  fvlist <- List.foldr (\e rec -> do
                          r <- rec
                          fv <- return $ free_var e
                          return (fv:r)) (return []) elist

  -- Type the inner expressions, and extract the constraints
  csetlist <- List.foldr (\(e, t, fv) rec -> do
                            cset <- rec
                            (typctx_fv, _) <- sub_context fv typctx
                            cset' <- constraint_typing typctx_fv e t
                            return $ cset <> cset') (return ([], [])) (List.zip3 elist tlist fvlist)

  -- Construction of all the constraints p <= f1 ... p <= fn
  pcons <- return $ List.map (\(TBang n _) -> (p, n)) tlist

  -- Construction of the constraints of delta
  disunion <- return $ disjoint_union fvlist

  (_, typctx_delta) <- sub_context disunion typctx
  fconstraints <- have_duplicable_context typctx_delta
  
  return $ csetlist <> ([TBang p (TTensor tlist) <: typ], pcons ++ fconstraints)


-- Tensor elim typing rule
--
--     G1, !ID |- t : !n<a, b>  [L]    G2, !ID, x : !na, y : !nb |- u : T  [L']
--   -----------------------------------------------------------------------------
--     G1, G2, !ID |- let <x, y> = t in u : T    [L u L' u {1 <= I}]
--

constraint_typing typctx (ELet rec p t u) typ = do
  -- Extract the free variables of t and u
  fvt <- return $ free_var t
  fvu <- return $ free_var u

  -- Give the corresponding sub contexts
  (typctx_fvt, _) <- sub_context fvt typctx
  (typctx_fvu, _) <- sub_context fvu typctx

  -- Create the type of the pattern
  (a, typctx_fvu', cseta) <- bind_pattern p typctx_fvu

  -- Type t with this type
  csett <- case rec of
             Recursive -> do
                 -- Isolate the bindings issued by the pattern in typctx_fvu
                 (typctx_p, _) <- sub_context (free_var p) typctx_fvu'
                 -- Add them into typctx_fvt
                 typctx_fvt' <- merge_contexts typctx_p typctx_fvt
                 constraint_typing typctx_fvt' t a

             Nonrecursive -> do
                 constraint_typing typctx_fvt t a 
  
  -- Type u
  csetu <- constraint_typing typctx_fvu' u typ
  
  -- Generate the flag constraints for the intersection
  (_, typctx_delta) <- sub_context ((fvt \\ fvu) ++ (fvu \\ fvt)) typctx
  flags <- context_annotation typctx_delta
  fconstraints <- return $ List.map (\(_, f) -> (1, f)) flags
  
  return $ csett <> csetu <> cseta <> ([], fconstraints)


-- Data typing rule
--
-- Assuming the type definition
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

constraint_typing typctx (EDatacon dcon e) typ = do
  -- Detailed information
  ex <- get_location

  -- Retrieve the definition of the data constructor, and instanciate its typing scheme
  dtype <- datacon_def dcon
  (dtype', cset) <- instanciate dtype

  case (dtype', e) of
    -- No argument given, the constructor is typed as is
    (TBang n _, Nothing) -> do
        -- Some information
        specify_expression n $ ActualOfE (EDatacon dcon Nothing)
        specify_location n ex

        return $ [dtype' <: typ] <> cset

    -- One argument given, and the constructor requires one
    (TBang _ (TArrow t u@(TBang n _)), Just e) -> do
        -- Some information
        specify_expression n $ ActualOfE (EDatacon dcon $ Just e)
        specify_location n ex
        
        csete <- constraint_typing typctx e t
        return $ [u <: typ] <> csete <> cset


-- Match typing rule
--
--          G1, !ID |- t : !p(!nA + !m B)              [L1]
--            G2, !ID, x : !nA |- u : V                [L2]
--            G2, !ID, y : !mB |- v : V                [L3]
-- ---------------------------------------------------
--  G1, G2, !ID |- match t with (x -> u | y -> v) : V  [L1 u L2 u L3 u {1 <= I, p <= n, p <= m}]
--

constraint_typing typctx (EMatch e blist) typ = do
  -- Extract the free type variables of e one the one part, and the bindings on the other part 
  fve <- return $ free_var e
  fvlist <- List.foldl (\rec (p, f) -> do
                          r <- rec
                          fv <- return $ free_var f \\ free_var p
                          return $ List.union fv r) (return []) blist
  
  -- Create the type of the expression e, and type e
  a <- new_type
  (typctx_fve, _) <- sub_context fve typctx
  csete <- constraint_typing typctx_fve e a

  -- Type each of the bindings
  (typctx_fvlist, _) <- sub_context fvlist typctx
  csetlist <- List.foldl (\rec (p, f) -> do
                            cset <- rec
                            (b, typctx_fvlist', csetb) <- bind_pattern p typctx_fvlist

                            cset' <- constraint_typing typctx_fvlist' f typ
                            return $ cset <> csetb <> cset' <> ([b <: a], [])) (return ([], [])) blist

  -- Generate the flag constraints for the intersection
  disunion <- return $ (fve \\ fvlist) ++ (fvlist \\ fve)
  (_, typctx_delta) <- sub_context disunion typctx
  flags <- context_annotation typctx_delta
  fconstraints <- return $ List.map (\(_, f) -> (1, f)) flags
  
  return $ csete <> csetlist <> ([], fconstraints) 


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
  
  -- Filter on the free variables of e and type e : e must have the type bool
  (typctx_fve, _) <- sub_context fve typctx
  csete <- constraint_typing typctx_fve e (TBang anyflag TBool)

  -- Filter on the free variables of f an g
  (typctx_fvfg, _) <- sub_context fvfg typctx

  -- Type f and g
  csetf <- constraint_typing typctx_fvfg f typ
  csetg <- constraint_typing typctx_fvfg g typ

  -- Generate the flag constraints for the intersection
  (_, typctx_delta) <- sub_context ((fve \\ fvfg) ++ (fvfg \\ fve)) typctx
  flags <- context_annotation typctx_delta
  fconstraints <- return $ List.map (\(_, f) -> (1, f)) flags
  
  return $ csete <> csetf <> csetg <> ([], fconstraints)



-- | Throw a typing error, based on the reference flags of the faulty types
-- The return type can be anything, since an exception will be thrown in any case
throw_TypingError :: Type -> Type -> QpState a
throw_TypingError t@(TBang n _) u@(TBang m _) = do
  -- Retrieve the location / expression of the types
  termn <- referenced_expression n
  termm <- referenced_expression m

  -- Print the types t and u
  prt <- return $ pprint t
  pru <- return $ pprint u

  -- See what information we have
  case (termn, termm) of
    (Just (e, ex), _) -> do
        -- Print the expression / pattern
        pre <- case e of
                 ActualOfE e -> return $ pprint e
                 ActualOfP p -> return $ pprint p

        throwQ $ DetailedTypingError prt pru pre ex 

    (_, Just (e, ex)) -> do
        -- Print the expression / pattern
        pre <- case e of
                 ActualOfE e -> return $ pprint e
                 ActualOfP p -> return $ pprint p

        throwQ $ DetailedTypingError pru prt pre ex 
 
    _ ->
      -- No information available
      throwQ $ TypingError prt pru



-- Break composite constrainst of the form :
  -- T -> U <: T' -> U'
  -- ! T <: ! U
break_composite :: ConstraintSet -> QpState ConstraintSet


-- Nothing to do
break_composite ([], lc) = return ([], lc)


-- With location
break_composite ((Subtype (TBang n (TLocated t _)) u):lc, fc) = do
  break_composite ((Subtype (TBang n t) u):lc, fc)

break_composite ((Subtype t (TBang n (TLocated u _))):lc, fc) = do
  break_composite ((Subtype t (TBang n u)):lc, fc)


-- Unit against unit : removed
break_composite ((Subtype (TBang _ TUnit) (TBang _ TUnit)):lc, fc) = do
  break_composite (lc, fc)


-- Bool against bool : removed
break_composite ((Subtype (TBang _ TBool) (TBang _ TBool)):lc, fc) = do
  break_composite (lc, fc)


-- Qbit against QBit : removed
break_composite ((Subtype (TBang n TQbit) (TBang m TQbit)):lc, fc) = do
  -- Make sure the qbit type is not banged
  if n >= 2 then unset_flag n
  else return ()
  if m >= 2 then unset_flag m
  else return ()
  
  break_composite (lc, fc)


-- Arrow against arrow
  -- T -> U <: T' -> U' 
-- Into
  -- T' <: T && U <: U'
break_composite ((Subtype (TBang n (TArrow t u)) (TBang m (TArrow t' u'))):lc, fc) = do
  break_composite ((Subtype t' t):(Subtype u u'):lc, (m, n):fc)
 

-- Tensor against tensor
  -- T * U <: T' * U'
-- Into
  -- T <: T' && U <: U'
break_composite ((Subtype (TBang p (TTensor tlist)) (TBang q (TTensor tlist'))):lc, fc) = do
  if List.length tlist == List.length tlist' then do
    comp <- return $ List.map (\(t, u) -> t <: u) $ List.zip tlist tlist'
    break_composite $ (comp, [(q, p)]) <> (lc, fc)

  else do
    throw_TypingError (TBang p (TTensor tlist)) (TBang q (TTensor tlist'))


-- User type against user type : removed
break_composite ((Subtype (TBang n (TUser utyp args)) (TBang m (TUser utyp' args'))):lc, fc) = do
  if utyp == utyp' && List.length args == List.length args' then do
    cset <- return $ List.map (\(t, u) -> t <: u) $ List.zip args args'
    break_composite $ (cset, [(m, n)]) <> (lc, fc)
  else
    throw $ TypingError (pprint (TUser utyp args)) (pprint (TUser utyp' args'))


-- Circ against Circ
  -- circ (T, U) <: circ (T', U')
-- Into
  -- T' <: T && U <: U'
-- The flags don't really matter, as they can take any value, so no constraint m <= n is generated
break_composite ((Subtype (TBang _ (TCirc t u)) (TBang _ (TCirc t' u'))):lc, fc) = do
  break_composite ((Subtype t' t):(Subtype u u'):lc, fc)


-- Semi composite (unbreakable) constraints
break_composite (c@(Subtype (TBang _ (TVar _)) _):lc, fc) = do
  (lc', fc') <- break_composite (lc, fc)
  return (c:lc', fc')

break_composite (c@(Subtype _ (TBang _ (TVar _))):lc, fc) = do
  (lc', fc') <- break_composite (lc, fc)
  return (c:lc', fc')


-- Everything else is a typing error
break_composite ((Subtype t u):lc, fc) = do
  throw_TypingError t u



-------------------------------------- UNIFICATION -----------------------------------------------------

-- Instanciation of model types
  -- The bang annotations of the model are ignored
model_of_lin :: LinType -> QpState LinType
model_of :: Type -> QpState Type
map_to_model :: Type -> Type -> QpState LinType
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
  return (TArrow t' u')

model_of_lin (TTensor tlist) = do
  tlist' <- List.foldr (\t rec -> do
                          r <- rec
                          t' <- model_of t
                          return (t':r)) (return []) tlist
  return (TTensor tlist')

model_of_lin (TUser n args) = do
  args' <- List.foldr (\a rec -> do
                         r <- rec
                         a' <- model_of a
                         return (a':r)) (return []) args
  return (TUser n args')

model_of_lin (TVar _) = do
  x <- fresh_type
  return (TVar x)

model_of_lin (TCirc t u) = do
  t' <- model_of t
  u' <- model_of u
  return (TCirc t' u')

model_of (TBang _ t) = do
  n <- fresh_flag
  t' <- model_of_lin t
  return $ TBang n t'

-------------
map_to_model (TBang _ (TVar x)) (TBang _ t) = do
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
                                                          Subtype tx@(TBang _ (TVar _)) _ -> List.elem tx cx
                                                          Subtype _ ty@(TBang _ (TVar _)) -> List.elem ty cx) lc
        
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
        (atomx, cset) -> do
            -- Select a composite type from the semi-composite constraints
            model <- case List.head cset of
                       Subtype (TBang _ (TVar _)) t -> return t
                       Subtype t (TBang _ (TVar _)) -> return t

            -- Map the youngest variables each to a new specimen of the model
            List.foldl (\rec x -> do
                          rec
                          _ <- map_to_model x model
                          return ()) (return ()) cx

            -- Rewrite and reduce the atomic constraints
            atomx' <- List.foldl (\rec (Subtype (TBang n (TVar x)) (TBang m (TVar y))) -> do
                                    atom <- rec
                                    xt <- appmap x
                                    yt <- appmap y
                                    atom' <- break_composite ([TBang n xt <: TBang m yt], [])
                                    return $ atom' <> atom) (return emptyset) atomx

            -- Rewrite and reduce the semi composite constraints
            cset' <- List.foldl (\rec c -> do
                                   cs <- rec
                                   case c of
                                     Subtype (TBang n (TVar x)) u -> do
                                         xt <- appmap x
                                         cs' <- break_composite ([TBang n xt <: u], [])
                                         return $ cs' <> cs

                                     Subtype t (TBang m (TVar y)) -> do
                                         yt <- appmap y
                                         cs' <- break_composite ([t <: TBang m yt], [])
                                         return $ cs' <> cs)  (return emptyset) cset


            -- Register the relations defined by those new constraints
            register_constraints $ fst atomx'
            register_constraints $ fst cset'

            -- Unify the rest
            unify $ atomx' <> cset' <> (non_lcx, fc)


            {-
            -- If all the constraints are chained as : T <: x1 <: .. <: xn <: U, make the approximation x1 = .. = xn = T, T <: U
            (ischain, sorted) <- return $ chain_constraints lcx
            
            if ischain then do
              newlog 0 "CHAINED"
              leftend <- case List.head sorted of
                           Subtype t _ -> return $ t
              rightend <- case List.last sorted of
                            Subtype _ t -> return t

              -- Map x1 .. xn to T or U
              case (leftend, rightend) of
                (TBang _ (TVar x), _) -> do
                    List.foldl (\rec (TBang n (TVar x)) -> do
                                  rec
                                  mapsto x $ no_bang rightend) (return ()) cx
                    -- Unify the rest
                    unify (non_lcx, fc)
                    
                (_, TBang _ (TVar x)) -> do
                    List.foldl (\rec (TBang n (TVar x)) -> do
                                  rec
                                  mapsto x $ no_bang leftend) (return ()) cx
                    -- Unify the rest
                    unify (non_lcx, fc)

                _ -> do
                    List.foldl (\rec (TBang n (TVar x)) -> do
                                  rec
                                  mapsto x $ no_bang leftend) (return ()) cx

                    (cset', fc') <- break_composite ([Subtype leftend rightend], fc)
                    register_constraints cset'
                    -- Unify the rest
                    unify (cset' ++ non_lcx, fc')

            else do           
              newlog 0 "UNCHAINED"
              
              onesided <- return $ is_one_sided cset
              -- If all the constraints are one-sided, make the approximation : x1 = .. = xn
              cset <- if onesided then do
                      newlog 0 "ONE SIDED"
                      (TBang _ (TVar cxh)) <- return $ List.head cx
                      List.foldl (\rec (TBang n (TVar x)) -> do
                                      rec
                                      mapsto x (TVar cxh)) (return ()) $ List.tail cx

                      return $ List.map (\c -> case c of
                                                 Subtype (TBang n (TVar _)) t -> Subtype (TBang n $ TVar cxh) t
                                                 Subtype t (TBang n (TVar _)) -> Subtype t (TBang n $ TVar cxh)) cset
                    else do
                      return cset


              model <- return $ constraint_unifier cset

              newlog 0 $ pprint model

            
              List.foldl (\rec (TBang _ (TVar x)) -> do
                             rec
                             _ <- map_to_model x $ no_bang model
                             return ()) (return ()) cx
            
              -- Rewrite and reduce the atomic constraints
              atomx' <- List.foldl (\rec (Subtype (TBang n (TVar x)) (TBang m (TVar y))) -> do
                                      (lr, fr) <- rec
                                      xt <- appmap x
                                      yt <- appmap y
                                      (lr', fr')  <- break_composite ([Subtype (TBang n xt) (TBang m yt)], fr)
                                      return (lr' ++ lr, fr')) (return (non_lcx, fc)) atomx

              -- Rewrite and reduce the remaining constraints
              (cset', fc'') <- List.foldl (\rec c -> do
                                     (lr, fr) <- rec
                                     c' <- case c of
                                             Subtype (TBang n (TVar x)) t -> do
                                                 xt <- appmap x
                                                 return $ Subtype (TBang n xt) t

                                             Subtype t (TBang n (TVar x)) -> do
                                                 xt <- appmap x
                                                 return $ Subtype t (TBang n xt)

                                     (lr', fr') <- break_composite ([c'], fr)
                                     return (lr' ++ lr, fr')) (return atomx') cset
              
              -- Register the new relations defined by those constraints
              register_constraints cset'

              -- Unifcation of the remaining
              unify (cset', fc'')
              -}


-- | Recursively applies the flag constraints until no deduction can be drewn
apply_constraints :: [FlagConstraint] -> QpState (Bool, [FlagConstraint])
-----------------------------------------------------------------------------------------------------------
apply_constraints [] = do
  return (False, [])

apply_constraints (c:cc) = do
  case c of
    (1, 0) -> do
        fail "Absurd constraint 1 <= 0"

    (n, 0) -> do
        unset_flag n
        (_, cc') <- apply_constraints cc
        return (True, cc')

    (1, m) -> do
        set_flag m
        (_, cc') <- apply_constraints cc
        return (True, cc')

    (m, n) -> do
        vm <- flag_value m
        vn <- flag_value n
        case (vm, vm) of
          (One, Zero) -> do
              fail "Absurd constraint 1 <= 0"

          (Unknown, Zero) -> do
              unset_flag m
              (_, cc') <- apply_constraints cc
              return (True, cc')
 
          (One, Unknown) -> do
              set_flag n
              (_, cc') <- apply_constraints cc
              return (True, cc')

          (Unknown, Unknown) -> do
              (b, cc') <- apply_constraints cc
              return (b, c:cc')

          _ -> do
              apply_constraints cc


solve_constraints :: [FlagConstraint] -> QpState [FlagConstraint]
-----------------------------------------------------------------------------------------------------
solve_constraints fc = do
  (b, fc') <- apply_constraints fc
  if b then
    solve_constraints fc'
  else
    return fc'


-- Solve the constraint set
solve_annotation :: [FlagConstraint] -> QpState ()
----------------------------------------------------------------
solve_annotation fc = do

  -- Elimination of trivial constraints f <= 1 and 0 <= f, -1 <= f and f <= -1
  fc' <- return $ List.filter (\(m, n) -> m /= 0 && n /= 1 && m /= -1 && n /= -1) fc

  -- Application of the constraints 1 <= f and f <= 0
  fc'' <- solve_constraints fc'

  return ()

