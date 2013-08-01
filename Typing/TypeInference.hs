-- | This module implements the constraint typing algorithm, and the unification algorithm.
module Typing.TypeInference where

import Prelude hiding (filter)

import Classes
import Utils

import Parsing.Localizing
import Parsing.Syntax (RecFlag (..))
import qualified Parsing.Syntax as S

import Typing.CoreSyntax
import Typing.TypingContext
import Typing.Ordering
import Typing.Subtyping
import Typing.TransSyntax

import Monad.QuipperError
import Monad.QpState
import Monad.Modules

import Control.Exception as E

import Data.List ((\\))
import qualified Data.List as List
import Data.Sequence as Seq hiding (filter)
import Data.Array as Array
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IMap


-- | Filters a set of flag constraints : removes the trivial constraints (n <= 1), (0 <= n), (-1 <= n), (n <= -1), and 
-- applies the constraints 1 <= n (resp. n <= 0) by setting the flag n to 1 (resp. 0).
filter :: [FlagConstraint] -> QpState [FlagConstraint]
filter fc = do
  List.foldl (\rec c -> do
                r <- rec
                case c of
                  -- Useless
                  (-1, _) -> return r
                  (_, -1) -> return r
                  (0, _) -> return r
                  (_, 1) -> return r

                  -- Direct
                  (1, n) -> do
                      set_flag n
                      return r
                  (n, 0) -> do
                      unset_flag n
                      return r

                  -- Everything else
                  _ -> return $ c:r) (return []) fc



-- | Builds the constraint typing derivation. The algorithm inputs and incomplete constraint typing judgement
-- G |- t : T_1 .. T_n, and produces the constraint set L such that the relation G |- t : T_1 .. T_n [L] holds.
-- The list of types T_1 .. T_n correponds to a set of upper bounds of the type of t. It is initially of size 1 and
-- can be increased via the expressions (e <: T) imposing that the type of e be a subtype of T.
constraint_typing :: TypingContext -> Expr -> [Type] -> QpState ConstraintSet

-- | Located things
-- Change the location and resume
constraint_typing gamma (ELocated e ex) cst = do
  set_location ex
  constraint_typing gamma e cst


-- | For builtins, get the type registered in the builtins map.
constraint_typing gamma (EBuiltin s) cst = do
  -- The context must be duplicable
  fconstraints <- force_duplicable_context gamma >>= filter

  acts <- builtin_type s
  return $ (acts <:: cst) <> fconstraints


-- | Unit typing rule
--
-- -------------------
--  !I G  |- * : !n T  [{1 <= I}]
--

constraint_typing gamma EUnit cst = do
  -- The context must be duplicable
  fconstraints <- force_duplicable_context gamma >>= filter
  
  -- Generates a referenced flag of the actual type of EUnit
  ex <- get_location
  n <- fresh_flag_with_value Any
  specify_expression n $ ActualOfE EUnit
  specify_location n ex

  return $ (TBang n TUnit <:: cst) <> fconstraints


-- | True / False typing rule
--
-- --------------------------------
--  !I G |- True / False : !n bool  [{1 <= I}]
-- 

constraint_typing gamma (EBool b) cst = do
  -- The context must be duplicable
  fconstraints <- force_duplicable_context gamma >>= filter

  -- Generates a referenced flag of the actual type of EBool
  ex <- get_location
  n <- fresh_flag_with_value Any
  specify_expression n $ ActualOfE (EBool b)
  specify_location n ex

  return $ (TBang n TBool <:: cst) <> fconstraints


-- | Int typing rule
--
-- --------------------------------
--  !I G |- Int : !n int  [{1 <= I}]
-- 

constraint_typing gamma (EInt p) cst = do
  -- The context must be duplicable
  fconstraints <- force_duplicable_context gamma >>= filter

  -- Generates a referenced flag of the actual type of EBool
  ex <- get_location
  n <- fresh_flag_with_value Any
  specify_expression n $ ActualOfE (EInt p)
  specify_location n ex

  return $ (TBang n TInt <:: cst) <> fconstraints


-- | Axiom typing rules
--
-- ---------------------
--  !IG, t : T |- t : U  [{T <: U, 1 <= I}]
--

constraint_typing gamma (EVar x) cst = do
  -- Retrieve the type of x from the typing context
  sa <- type_of x gamma
  (a, csetx) <- instanciate sa -- In case a is a typing scheme

  -- Have the rest of the context be duplicable
  (_, gamma_nx) <- sub_context [x] gamma
  fconstraints <- force_duplicable_context gamma_nx >>= filter

  return $ (a <:: cst) <> fconstraints <> csetx


constraint_typing gamma (EGlobal x) cst = do
  -- Retrieve the type of x from the typing context
  sa <- type_of_global x
  (a, csetx) <- instanciate sa -- In case a is a typing scheme

  -- Have the rest of the context be duplicable
  fconstraints <- force_duplicable_context gamma >>= filter

  return $ (a <:: cst) <> fconstraints <> csetx



-- | Box typing rule
--
-- ------------------------------------------------------
--  !I G |- box[T] :  !n (!1 (T -> U) -> !n Circ (T, U))  [L u {1 <= I}]
--

constraint_typing gamma (EBox (TForall _ _ cset a)) cst = do
  -- The context must be duplicable 
  fconstraints <- force_duplicable_context gamma >>= filter

  -- Flag reference
  ex <- get_location
  n <- fresh_flag_with_value Any
  specify_expression n $ ActualOfE (EBox a)
  specify_location n ex

  -- Build the type of box
  b <- new_type  
  arw <- return $ TBang one (TArrow a b)
  cir <- return $ TBang anyflag (TCirc a b)

  return $ cset <> (TBang n (TArrow arw cir) <:: cst) <> fconstraints
  

-- | Rev typing rule
--
-- --------------------------------------------
--  G |- rev : !n (!n Circ (T, U) -> !n Circ (U, T))  [L]
--

constraint_typing gamma ERev cst = do
  -- The context must be duplicable
  fconstraints <- force_duplicable_context gamma >>= filter

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

  return $ (TBang n (TArrow cirab cirba) <:: cst) <> fconstraints


-- | Unbox typing rule
--    
-- ------------------------------------------------
--  G |- unbox : !1 (!n circ(T, U) -> !1 (T -> U))  [L]
--

constraint_typing gamma EUnbox cst = do
  -- The context must be duplicable
  fconstraints <- force_duplicable_context gamma >>= filter

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

  return $ (TBang n (TArrow cir arw) <:: cst) <> fconstraints


-- App typing rule
--
--  G1, !ID |- t : a -> T   [L] 
--     G2, !ID |- u : a     [L']
-- ------------------------
--  G1, G2, !ID |- t u : T  [L u L' u {1 <= I}]
--

constraint_typing gamma (EApp t u) cst = do
  -- Create the type of the argument
  a <- new_type

  -- Extract the free variables of t and u
  fvt <- return $ free_var t
  fvu <- return $ free_var u

  -- Filter on the free variables of t and type t
  -- The constraints on the actual type of the application are transformed into constraints
  -- on the type of the function
  (gamma_t, _) <- sub_context fvt gamma
  csett <- constraint_typing gamma_t t (List.map (\t -> TBang 0 $ TArrow a t) cst)

  -- Filter on the free variables of u and type u
  (gamma_u, _) <- sub_context fvu gamma
  csetu <- constraint_typing gamma_u u [a]

  -- Construction of the constraint for !I Delta, the intersection of Gt and Gu
  disunion <- return $ disjoint_union [fvt, fvu]
  (_, delta) <- sub_context disunion gamma
  fconstraints <- force_duplicable_context delta >>= filter
  
  return $ csett <> csetu <> fconstraints


-- Lambda typing rule
--
--    !IG, x : a |- t : b     [L]
-- --------------------------
--  !IG |- \x.t : !n(a -> b)  [L u {n <= Ii}]
--

constraint_typing gamma (EFun p e) cst = do
  -- Detailed information on the type of the function 
  ex <- get_location
  n <- fresh_flag
  specify_expression n $ ActualOfE (EFun p e)
  specify_location n ex

  -- Context annotations (without the pattern's bindings)
  flags <- context_annotation gamma
  
  -- Bind p in the current context - this returns the type a of the argument of the abstraction
  (a, gamma_p, csetp) <- bind_pattern p
  b <- new_type

  -- Type the expression e
  csete <- constraint_typing (gamma_p <+> gamma) e [b]

  -- Build the context constraints : n <= I
  fconstraints <- (return $ List.map (\(_, f) -> (n, f)) flags) >>= filter

  return $ csetp <> csete <> (TBang n (TArrow a b) <:: cst) <> fconstraints


-- Tensor intro typing rule
--
--    G1, !ID |- t : !n a      [L]
--    G2, !ID |- u : !n b      [L']
-- ---------------------------
--  G1, G2, !ID |- <t, u> : T  [L u L' u {1 <= I} u {!n (a * b) <: T}]
--

constraint_typing gamma (ETuple elist) cst = do
  -- Detailed information of the type of the tuple
  ex <- get_location
  p <- fresh_flag
  specify_expression p $ ActualOfE (ETuple elist)
  specify_location p ex 

  -- Create n new types
  tlist <- List.foldr (\_ rec -> do
                         r <- rec
                         t <- new_type
                         return (t:r)) (return []) elist

  -- Extract the free variables of all the inner expressions
  fvlist <- List.foldr (\e rec -> do
                          r <- rec
                          fv <- return $ free_var e
                          return (fv:r)) (return []) elist

  -- Type the inner expressions, and extract the constraints
  csetlist <- List.foldr (\(e, t, fv) rec -> do
                            cset <- rec
                            (gamma_fv, _) <- sub_context fv gamma
                            cset' <- constraint_typing gamma_fv e [t]
                            return $ cset <> cset') (return ([], [])) (List.zip3 elist tlist fvlist)

  -- Construction of all the constraints p <= f1 ... p <= fn
  pcons <- (return $ List.map (\(TBang n _) -> (p, n) :: FlagConstraint) tlist) >>= filter

  -- Construction of the constraints of delta
  disunion <- return $ disjoint_union fvlist
  (_, delta) <- sub_context disunion gamma
  fconstraints <- force_duplicable_context delta >>= filter
  
  return $ csetlist <> (TBang p (TTensor tlist) <:: cst) <> pcons <> fconstraints


-- Tensor elim typing rule, generalized to work with any kind of pattern
--
--     G1, !ID |- t : !n<a, b>  [L]    G2, !ID, x : !na, y : !nb |- u : T  [L']
--   -----------------------------------------------------------------------------
--     G1, G2, !ID |- let <x, y> = t in u : T    [L u L' u {1 <= I}]
--
-- With the let polymorphism, the typing rule becomes the following
--
--             G1, !ID |- t : T               [L]
--      G2, !ID, p : forall A, L=>T |- u : U  [L']
--   ----------------------------------------
--        G1, G2, !ID |- let p = t in u : T   [L u L' u {1 <= I}]
--
--  where A = free variables of T \\ free_variables of G1, !ID
--

constraint_typing gamma (ELet rec p t u) cst = do
  -- Extract the free variables of t and u
  fvt <- return $ free_var t
  fvu <- return $ free_var u

  -- Give the corresponding sub contexts
  (gamma_t, _) <- sub_context fvt gamma
  (gamma_u, _) <- sub_context fvu gamma

  -- Mark the limit free variables / bound variables used in the typing of t
  limtype <- get_context >>= return . type_id
  limflag <- get_context >>= return . flag_id

  -- Create the type of the pattern
  (a, gamma_p, csetp) <- bind_pattern p

  -- Type t with this type
  csett <- case rec of
             Recursive -> do
                 -- Add the bindings of the pattern into gamma_fvt
                 constraint_typing (gamma_p <+> gamma_t) t [a]

             Nonrecursive -> do
                 -- If not recursive, do nothing
                 constraint_typing gamma_t t [a]

  -- Last of the free variables of t
  endtype <- get_context >>= return . type_id
  endflag <- get_context >>= return . flag_id
 
  -- Unify the constraints produced by the typing of t (exact unification)
  cs <- break_composite True (csetp <> csett)  -- Break the composite constraints
  register_constraints $ fst cs                -- Initialize the variable ordering
  csett <- unify True cs                       -- Unify

  -- Apply the substitution produced by the unification of csett to the context gamma_u
  gamma_u <- IMap.foldWithKey (\x a rec -> do
                                 m <- rec
                                 a' <- map_type a
                                 return $ IMap.insert x a' m) (return IMap.empty) gamma_u


  -- Generalize the types of the pattern (= polymorphism)
  gamma_p <- IMap.foldWithKey (\x a rec -> do
                                  ctx <- rec
                                  -- First apply the substitution
                                  a' <- map_type a

                                  -- Generalize over its free variables, the free variables form a subset of those used
                                  -- here, but it would be too annoying to recompute them.
                                  gena <- return $ TForall [limflag .. endflag-1] [limtype .. endtype-1] csett a'

                                  -- Update the global variables
                                  update_global_type x gena

                                  -- Update the typing context of u
                                  return $ IMap.insert x gena ctx) (return IMap.empty) gamma_p

  -- Type u - The constraints on the type of the let are transfered to the type of u
  csetu <- constraint_typing (gamma_p <+> gamma_u) u cst
  
  -- Generate the flag constraints for the intersection
  disunion <- return $ disjoint_union [fvt, fvu]
  (_, delta) <- sub_context disunion gamma
  fconstraints <- force_duplicable_context delta >>= filter
  
  return $ csetu <> fconstraints


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

constraint_typing gamma (EDatacon dcon e) cst = do
  -- Extent of the expression
  ex <- get_location

  -- Retrieve the definition of the data constructor, and instanciate its typing scheme
  dtype <- datacon_def dcon
  (dtype', csetd) <- instanciate dtype

  case (dtype', e) of
    -- No argument given, the constructor is typed as is
    (TBang n _, Nothing) -> do
        -- Some information
        specify_expression n $ ActualOfE (EDatacon dcon Nothing)
        specify_location n ex

        -- The context must be duplicable
        fconstraints <- force_duplicable_context gamma >>= filter

        return $ (dtype' <:: cst) <> csetd <> fconstraints

    -- One argument given, and the constructor requires one
    (TBang _ (TArrow t u@(TBang n _)), Just e) -> do
        -- Some information
        specify_expression n $ ActualOfE (EDatacon dcon $ Just e)
        specify_location n ex
        
        -- Type the argument of the data constructor
        csete <- constraint_typing gamma e [t]

        return $ (u <:: cst) <> csete <> csetd


-- Match typing rule
--
--          G1, !ID |- t : !p(!nA + !m B)              [L1]
--            G2, !ID, x : !nA |- u : V                [L2]
--            G2, !ID, y : !mB |- v : V                [L3]
-- ---------------------------------------------------
--  G1, G2, !ID |- match t with (x -> u | y -> v) : V  [L1 u L2 u L3 u {1 <= I, p <= n, p <= m}]
--

constraint_typing gamma (EMatch e blist) cst = do
  -- Extract the free type variables of e one the one part, and the bindings on the other part 
  fve <- return $ free_var e
  fvlist <- List.foldl (\rec (p, f) -> do
                          r <- rec
                          fv <- return $ free_var f \\ free_var p
                          return $ List.union fv r) (return []) blist
  
  -- Create the type of the expression e, and type e
  a <- new_type
  (gamma_e, _) <- sub_context fve gamma
  csete <- constraint_typing gamma_e e [a]

  -- Type each of the bindings
  (gamma_bl, _) <- sub_context fvlist gamma
  csetlist <- List.foldl (\rec (p, f) -> do
                            cset <- rec
                            -- Bind the pattern p
                            (b, gamma_p, csetp) <- bind_pattern p

                            -- Type the associated expression, with the same constraints cst as the original expression
                            -- Refer to the case of 'if' for more clarity.
                            csetf <- constraint_typing (gamma_p <+> gamma_bl) f cst

                            -- The type of the pattern must be subtype of the type of the expression e
                            return $ cset <> csetp <> csetf <> [b <: a]) (return emptyset) blist

  -- Generate the flag constraints for the intersection
  disunion <- return $ disjoint_union [fve, fvlist]
  (_, delta) <- sub_context disunion gamma
  fconstraints <- force_duplicable_context delta >>= filter
  
  return $ csete <> csetlist <> fconstraints


-- Typing rule (if)
--
--     G1, !ID |- e : bool                 [L]
--       G2, !ID |- f : T                  [L']
--       G2, !ID |- g : T                  [L'']
-- ---------------------------------------
--  G1, G2, !ID |- if e then f else g : T  [L u L' u L'' u {1 <= I}]
--
-- Same as pattern matchings (since it is only a special case with the type bool = True | False

constraint_typing gamma (EIf e f g) cst = do
  -- Extract the free variables of e, f and g
  fve <- return $ free_var e
  fvfg <- return $ List.union (free_var f) (free_var g)
  
  -- Filter on the free variables of e and type e : e must have the type bool
  (gamma_e, _) <- sub_context fve gamma
  csete <- constraint_typing gamma_e e [TBang anyflag TBool]

  -- Filter on the free variables of f an g. f and g must have the same type as the whole expression, so they
  -- inherit the same constraints.
  (gamma_fg, _) <- sub_context fvfg gamma
  csetf <- constraint_typing gamma_fg f cst
  csetg <- constraint_typing gamma_fg g cst

  -- Generate the flag constraints for the context delta
  disunion <- return $ disjoint_union [fve, fvfg]
  (_, delta) <- sub_context disunion gamma
  fconstraints <- force_duplicable_context delta >>= filter
  
  return $ csete <> csetf <> csetg <> fconstraints


-- No typing rule, but a constraint on the type of the expression, of the form
--      e <: T   <==>   type of e <: T
-- The translation of the constraint type has been delayed up until there
-- to be able to generalize over the free variables of this type in the let-polymorphism
constraint_typing gamma (EConstraint e t) cst = do
  (t', cset) <- translate_unbound_type t
  csete <- constraint_typing gamma e (t':cst)
  return $ cset <> csete




-------------------------------------- UNIFICATION ----------------------

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

model_of_lin TInt = do
  return TInt

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

-- | Unification algorithm
-- The boolean argument specify whether the result must be exact, or if approximations
-- can be made
unify :: Bool -> ConstraintSet -> QpState ConstraintSet
unify exact (lc, fc) = do
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
      newlog 1 logx
      newlog 1 lognonx
                                             
      -- Filter the atomic constraints
      (atomx, natomx) <- return $ List.partition is_atomic lcx

      -- The atomic constraints still convey some flag constraints
      fcatom <- List.foldl (\rec (Subtype (TBang n _) (TBang m _)) -> do
                              r <- rec
                              return $ (m, n):r) (return []) atomx

      -- Check the next action
      case (atomx, natomx) of

        -- No semi-composite constraints : trivial solution with x1 = .. = xn,  unify the rest
        (atomx, []) -> do

            if not exact then do

              -- APPROXIMATION :
              -- Of all the variables, keep only one and replace the rest
              ((TBang n xh):rest) <- return cx
              List.foldl (\rec (TBang m (TVar x)) -> do 
                            rec
                            mapsto x $ xh) (return ()) rest
              unify exact (non_lcx, fcatom ++ fc)

            else do

              -- EXACT :
              -- Unify the rest, and keep the atomic constraints untouched
              (non_lcx', fc') <- unify exact (non_lcx, fc)
              return (non_lcx' ++ atomx, fc')

        -- Semi-composite constraints :
        (atomx, cset) -> do
            
            (ischain, sorted) <- return $ chain_constraints lcx
            if not exact && ischain then do

              -- APPROXIMATION :
              -- When all the constraints are chained as : T <: x1 <: .. <: xn <: U, make the approximation x1 = .. = xn = T, T <: U
              newlog 1 "APPROX: CHAINED"

              -- Get the left and right ends of the chain of constraints
              leftend <- case List.head sorted of
                           Subtype t _ -> return $ t
              rightend <- case List.last sorted of
                            Subtype _ t -> return t

              -- One of the ends must be composite
              case (leftend, rightend) of
                (TBang _ (TVar x), _) -> do
                    -- Map everything to the right end
                    List.foldl (\rec (TBang n (TVar x)) -> do
                                  rec
                                  mapsto x $ no_bang rightend) (return ()) cx

                    -- Unify the rest
                    unify False (non_lcx, fcatom ++ fc)
                    
                (_, TBang _ (TVar x)) -> do
                    -- Map everything to the left end
                    List.foldl (\rec (TBang n (TVar x)) -> do
                                  rec
                                  mapsto x $ no_bang leftend) (return ()) cx

                    -- Unify the rest
                    unify False (non_lcx, fcatom ++ fc)

                _ -> do
                    -- Map everything to the left end
                    List.foldl (\rec (TBang n (TVar x)) -> do
                                  rec
                                  mapsto x $ no_bang leftend) (return ()) cx

                    -- Add the constraint  leftend <: rightend
                    cset' <- break_composite True ([leftend <: rightend], [])
                    register_constraints $ fst cset'

                    -- Unify the rest
                    unify False $ cset' <> (non_lcx, fcatom ++ fc)

            else do

              -- EXACT SOLUTION :
              -- Select a composite type from the semi-composite constraints
              newlog 1 "EXACT"
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
                                      atom' <- break_composite True ([TBang n xt <: TBang m yt], [])
                                      return $ atom' <> atom) (return emptyset) atomx

              -- Rewrite and reduce the semi composite constraints
              cset' <- List.foldl (\rec c -> do
                                     cs <- rec
                                     case c of
                                       Subtype (TBang n (TVar x)) u -> do
                                           xt <- appmap x
                                           cs' <- break_composite True ([TBang n xt <: u], [])
                                           return $ cs' <> cs

                                       Subtype t (TBang m (TVar y)) -> do
                                           yt <- appmap y
                                           cs' <- break_composite True ([t <: TBang m yt], [])
                                           return $ cs' <> cs)  (return emptyset) cset


              -- Register the relations defined by those new constraints
              register_constraints $ fst atomx'
              register_constraints $ fst cset'

              -- Unify the rest
              unify exact $ atomx' <> cset' <> (non_lcx, fc)


            {-
            
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

