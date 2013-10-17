-- | This module implements the constraint typing algorithm and the unification algorithm.
module Typing.TypeInference where

import Prelude hiding (filter)

import Classes
import Utils

import Parsing.Location
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


-- | Filter a set of flag constraints. This removes the trivial constraints (/n/ <= 1), (0 <= /n/), (-1 <= /n/), (/n/ <= -1), and 
-- applies the constraints 1 <= /n/ (resp. /n/ <= 0) by setting the flag /n/ to 1 (resp. 0).
filter :: [FlagConstraint] -> QpState [FlagConstraint]
filter fc = do
  List.foldl (\rec c -> do
                r <- rec
                case c of
                  -- Useless
                  Le 0 _ _ -> return r
                  Le _ 1 _ -> return r

                  -- Direct
                  Le 1 n info -> do
                      set_flag n info
                      return r
                  Le n 0 info -> do
                      unset_flag n info
                      return r

                  -- Everything else
                  _ -> return $ c:r) (return []) fc



-- | Generalize a type, associated with constraints, over its free variables and flags.
-- The free variables of the type are those that are greater or equal to a limit type\/flag.
make_polymorphic_type :: Type                                  -- ^ Generic type.
                      -> ConstraintSet                         -- ^ Unreduced constraint set.
                      -> (RefFlag -> Bool, Variable -> Bool)   -- ^ Two functions stating whether a reference flag / variable is to be generalized over.
                      -> QpState TypeScheme
make_polymorphic_type typ (lc, fc) (isref, isvar) = do
  let (ff, fv) = (free_flag typ, free_typ_var typ)
  -- A variable / flag is to be kept (in the constraints) if it is from the context, or if it is in the final type.
  let (keepref, keepvar) = (\f -> (not $ isref f) || List.elem f ff, \v -> (not $ isvar v) || List.elem v fv)
     
  -- Walk starting from one point, stopping on the other important vertices
  -- origin : origin of the walk
  -- next : the set of vertices to visit next
  -- g : the graph
  -- visited : the set of vertices that have already been visited
  -- keep : function that says whether a vertice is important or not
  -- map : action to do when a non important vertex is being visited
  let walk = \origin next g visited keep map -> do
        case next of
          [] -> return []
          node:rest -> do
              let next = case IMap.lookup node g of
                    Nothing -> []
                    Just s -> s
              (nx, nc) <- List.foldl (\rec n -> do
                    (nx, nc) <- rec
                    -- Already treated, omit
                    if List.elem n visited then
                      return (nx,nc)
                    -- The vertex is important, write down the new constraint (origin, n)
                    else if keep n then
                      return (nx, (origin,n):nc)
                    -- The vertex is not important, map it to the origin
                    else do
                      map n origin
                      return (n:nx, nc)) (return ([],[])) next
              wnc <- walk origin (nx ++ rest) g (node:visited) keep map
              return $ nc ++ wnc

  -- Apply the walk function to all the important vertices
  let walk_all = \vertices g keep map ->
        List.foldl (\rec ori -> do
              nc <- rec
              case IMap.lookup ori g of
                Nothing -> return nc
                Just s -> do
                    wnc <- walk ori s g [ori] keep map
                    return $ wnc ++ nc) (return []) vertices

   -- Flags
  let g = List.foldl (\g (Le x y _) ->
        case IMap.lookup x g of
          Just c -> IMap.insert x (y:c) g
          Nothing -> IMap.insert x [y] g) IMap.empty fc

  let initf = List.filter keepref $ IMap.keys g
  cs <- walk_all initf g keepref (\_ _ -> return ())
  let fc' = List.map (\(n,m) -> Le n m no_info) cs

  -- Types
  let g = List.foldl (\g c -> 
        case c of
          Sublintype (TVar x) (TVar y) _ ->
              case IMap.lookup x g of
                Just c -> IMap.insert x (y:c) g
                Nothing -> IMap.insert x [y] g
          _ -> throw $ ProgramError "Unexpected unreduced constraint in function make_polymorphic_type") IMap.empty lc
 
  let initv = List.filter keepvar $ IMap.keys g
  cs' <- walk_all initv g keepvar (\a b -> mapsto a (TVar $ List.head fv)) 
  let lc' = List.map (\(n,m) -> Sublintype (TVar n) (TVar m) no_info) cs'

  -- Build the polymorphic type
  genfv <- return $ List.filter isvar fv
  genff <- return $ List.filter isref ff
  
  return $ TForall genff genfv (lc',fc') typ



-- | Build the constraint typing derivation. The algorithm inputs an incomplete constraint typing judgment
-- /G/ |- /t/ : /T/_1 .. /T/_/n/, and produces the constraint set /L/ such that the relation /G/ |- /t/ : /T/_1 .. /T/_/n/ [/L/] holds.
-- The list of types /T/_1 .. /T/_/n/ corresponds to a set of upper bounds of the type of /t/. It is initially of size 1 and
-- can be increased via the expressions (/e/ <: /T/) imposing that the type of /e/ be a subtype of /T/.
-- The constraint typing relations are (case by case):
--
-- Terms of the simply-typed lambda calculus:
--
-- @
--   ------------------------------------------- (ax)
--    !I G, x : T  |- x : U  [{1 <= I, T <: U}]
-- @
--
-- @
--                   !I G, x : !n a |- t : !m b  [L]
--   --------------------------------------------------------------- (abs)
--    !I G |- fun x -> t : T  [L u {p \<= I, !p(!n a -\> !m b) <: T}]
-- @
--
-- @
--    Gt |- t : !0(!n a -> T)   [L]            
--    Gu |- u : !n a            [L']        G \\ (t+u) = !I D
--   -------------------------------------------------------- (app)
--           G |- t u : T     [L u L' u {1 <= I}]
-- @
--
-- Tensor rules:
--
-- @
--   ---------------------------------------- (1)
--    !I G  |- * : T  [{1 <= I, !1 () <: T}]
-- @
--
-- @
--            Gt |- t : !n a   [L]
--            Gu |- u : !m b   [L']          G \\ (t+u) = !I D
--   --------------------------------------------------------------------- (*.I)
--    G |- \<t, u\> : !p(!n a * !m b)   [L u L' u {1 <= I, p <= n, p <= m}]
-- @
--
-- @
--    Gt |- t : !p(!n a * !m b)           [L]
--    Gu, x : !n a, y : !m b |- u : T     [L']            G \\ (t+u) = !I D
--   ----------------------------------------------------------------------- (*.E)
--    G |-  let \<x, y\> = t in u : T     [L u L' u {1 <= I, p <= n, p <= m}]
-- @
--
-- Boolean rules:
--
-- @
--   --------------------------------------------- (top)
--    !I G  |- true : T  [{1 <= I, !1 bool <: T}]
-- @
--
-- @
--   ---------------------------------------------- (bot)
--    !I G  |- false : T  [{1 <= I, !1 bool <: T}]
-- @
--
-- @
--    Gt |- t : !0 bool   [L]
--    Gu,v |- u : T       [L']          
--    Gu,v |- v : T       [L'']            G \\ (t+(u,v)) = !I D
--   ------------------------------------------------------------ (if)
--     G |- if t then u else v : T     [L u L' u L'' u {1 <= I}]
-- @
--
-- Circuit constructors: 
--
-- @
--   ----------------------------------------------------------------------------- (box)
--    !I G |- box[T] : U   [{1 \<= I, !1(!1(T -> !n a) -> !1 circ(T, !n a)) <: U}]
-- @
--
-- @
--   ----------------------------------------------------------------------------------- (unbox)
--    !I G |- unbox : T   [{1 \<= I, !1(!0 circ (!n a, !m b) -> !1(!n a -> !m b)) <: U}]
-- @
--
-- @
--   -------------------------------------------------------------------------------------- (rev)
--    !I G |- rev : U   [{1 \<= I, !1(!0 circ (!n a, !m b) -> !1 circ (!m b, !n a)) <: U}]
-- @
constraint_typing :: TypingContext -> Expr -> [Type] -> QpState ConstraintSet

-- For builtins, get the type registered in the builtins map.
constraint_typing gamma (EBuiltin ref s) cst = do
  -- The context must be duplicable
  duplicable_context gamma

  info <- return $ no_info { c_ref = ref }
  acts <- builtin_type s
  update_ref ref (\ri -> Just ri { r_type = acts })

  return $ ((acts <:: cst) & info, [])


-- | Unit typing rule
--
-- -------------------
--  !I G  |- * : !n T  [{1 <= I}]
--

constraint_typing gamma (EUnit ref) cst = do
  -- The context must be duplicable
  duplicable_context gamma
  
  -- Generates a referenced flag of the actual type of EUnit
  info <- return $ no_info { c_ref = ref }
  update_ref ref (\ri -> Just ri { r_type = TBang 1 TUnit })

  return $ ((TBang 1 TUnit <:: cst) & info, [])


-- | True / False typing rule
--
-- --------------------------------
--  !I G |- True / False : !n bool  [{1 <= I}]
-- 

constraint_typing gamma (EBool ref b) cst = do
  -- The context must be duplicable
  duplicable_context gamma

  -- Generates a referenced flag of the actual type of EBool
  info <- return $ no_info { c_ref = ref }
  update_ref ref (\ri -> Just ri { r_type = TBang 1 TBool })

  return $ ((TBang 1 TBool <:: cst) & info, [])


-- | Int typing rule
--
-- --------------------------------
--  !I G |- Int : !n int  [{1 <= I}]
-- 

constraint_typing gamma (EInt ref p) cst = do
  -- The context must be duplicable
  duplicable_context gamma

  -- Generates a referenced flag of the actual type of EBool
  info <- return $ no_info { c_ref = ref }
  update_ref ref (\ri -> Just ri { r_type = TBang 1 TInt })  

  return $ ((TBang 1 TInt <:: cst) & info, [])


-- | Axiom typing rules
--
-- ---------------------
--  !IG, t : T |- t : U  [{T <: U, 1 <= I}]
--

constraint_typing gamma (EVar ref x) cst = do
  -- Retrieve the type of x from the typing context
  sa <- type_of x gamma
  (a, csetx) <- instantiate sa

  -- Have the rest of the context be duplicable
  (_, gamma_nx) <- sub_context [x] gamma
  duplicable_context gamma_nx

  -- Information
  info <- return $ no_info { c_ref = ref }
  update_ref ref (\ri -> Just ri { r_type = a })

  return $ ((a <:: cst) & info) <> (csetx & info { c_type = Just a })


constraint_typing gamma (EGlobal ref x) cst = do
  -- Retrieve the type of x from the typing context
  sa <- type_of_global x
  (a, csetx) <- instantiate sa -- In case a is a typing scheme

  -- Have the rest of the context be duplicable
  duplicable_context gamma

  -- Information
  info <- return $ no_info { c_ref = ref }
  update_ref ref (\ri -> Just ri { r_type = a })

  return $ ((a <:: cst) & info) <> (csetx & info { c_type = Just a })



-- | Box typing rule
--
-- ------------------------------------------------------
--  !I G |- box[T] :  !n (!1 (T -> U) -> !n Circ (T, U))  [L u {1 <= I}]
--

constraint_typing gamma (EBox ref a) cst = do
  -- The context must be duplicable 
  duplicable_context gamma

  -- Information
  info <- return $ no_info { c_ref = ref }

  -- Build the type of box
  b <- new_type
  arw <- return $ TBang 1 (TArrow a b)
  cir <- return $ TBang 1 (TCirc a b)

  update_ref ref (\ri -> Just ri { r_type = TBang 1 (TArrow arw cir) })

  return ((TBang 1 (TArrow arw cir) <:: cst) & info, [])
  

-- | Rev typing rule
--
-- --------------------------------------------
--  G |- rev : !n (!n Circ (T, U) -> !n Circ (U, T))  [L]
--

constraint_typing gamma (ERev ref) cst = do
  -- The context must be duplicable
  duplicable_context gamma

  -- Information
  info <- return $ no_info { c_ref = ref }

  -- Build the type of rev
  a <- new_type
  b <- new_type
  cirab <- return $ TBang 0 (TCirc a b)
  cirba <- return $ TBang 1 (TCirc b a)

  update_ref ref (\ri -> Just ri { r_type = TBang 1 (TArrow cirab cirba) })

  return $ ((TBang 1 (TArrow cirab cirba) <:: cst) & info, [])


-- | Unbox typing rule
--    
-- ------------------------------------------------
--  G |- unbox : !1 (!n circ(T, U) -> !1 (T -> U))  [L]
--

constraint_typing gamma (EUnbox ref) cst = do
  -- The context must be duplicable
  duplicable_context gamma

  -- Flag reference
  info <- return $ no_info { c_ref = ref }

  -- Build the type of unbox
  a <- new_type
  b <- new_type
  arw <- return $ TBang 1 (TArrow a b)
  cir <- return $ TBang 0 (TCirc a b)

  update_ref ref (\ri -> Just ri { r_type = TBang 1 (TArrow cir arw) })

  return $ ((TBang 1 (TArrow cir arw) <:: cst) & info, [])


-- App typing rule
--
--  G1, !ID |- t : a -> T   [L] 
--     G2, !ID |- u : a     [L']
-- ------------------------
--  G1, G2, !ID |- t u : T  [L u L' u {1 <= I}]
--

constraint_typing gamma (EApp _ t u) cst = do
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
  disunion <- return $ linear_union [fvt, fvu]
  (_, delta) <- sub_context disunion gamma
  duplicable_context delta
 
  return $ csett <> csetu


-- Lambda typing rule
--
--    !IG, x : a |- t : b     [L]
-- --------------------------
--  !IG |- \x.t : !n(a -> b)  [L u {n <= Ii}]
--

constraint_typing gamma (EFun ref p e) cst = do
  -- Detailed information on the type of the function 
  n <- fresh_flag
  info <- return $ no_info { c_ref = ref }

  -- Context annotations (without the pattern's bindings)
  flags <- context_annotation gamma
  
  -- Bind p in the current context - this returns the type a of the argument of the abstraction
  (a, gamma_p, csetp) <- bind_pattern p
  b <- new_type

  -- Type the expression e
  csete <- constraint_typing ((IMap.map typescheme_of_type gamma_p) <+> gamma) e [b]

  -- Build the context constraints: n <= I
  fconstraints <- (return $ List.map (\(_, f) -> Le n f info) flags) >>= filter

  update_ref ref (\ri -> Just ri { r_type = TBang n (TArrow a b) })

  return $ (csetp & info) <> csete <> ((TBang n (TArrow a b) <:: cst) & info) <> fconstraints


-- Tensor intro typing rule
--
--    G1, !ID |- t : !n a      [L]
--    G2, !ID |- u : !n b      [L']
-- ---------------------------
--  G1, G2, !ID |- <t, u> : T  [L u L' u {1 <= I} u {!n (a * b) <: T}]
--

constraint_typing gamma (ETuple ref elist) cst = do
  -- Detailed information of the type of the tuple
  p <- fresh_flag
  info <- return $ no_info { c_ref = ref }

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
  pcons <- (return $ List.map (\(TBang n _) -> Le p n info) tlist) >>= filter

  -- Construction of the constraints of delta
  disunion <- return $ linear_union fvlist
  (_, delta) <- sub_context disunion gamma
  duplicable_context delta

  update_ref ref (\ri -> Just ri { r_type = TBang p (TTensor tlist) })
  
  return $ csetlist <> ((TBang p (TTensor tlist) <:: cst) & info) <> pcons


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

constraint_typing gamma (ELet _ rec p t u) cst = do
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
                 constraint_typing ((IMap.map typescheme_of_type gamma_p) <+> gamma_t) t [a]

             Nonrecursive -> do
                 -- If not recursive, do nothing
                 constraint_typing gamma_t t [a]

  -- -- POLYMORPHISM -- --
  -- If the expression is a VALUE, then the type can be generic.
  if is_value t then do
    -- Unify the constraints produced by the typing of t (exact unification)
    cs <- break_composite True (csetp <> csett)  -- Break the composite constraints
    csett <- unify True cs                       -- Unify

    -- Apply the substitution produced by the unification of csett to the context gamma_u
    gamma_u <- IMap.foldWithKey (\x a rec -> do
                                   m <- rec
                                   a' <- map_typescheme a
                                   return $ IMap.insert x a' m) (return IMap.empty) gamma_u

    -- Apply the substitution to the context gamma_p
    gamma_p <- IMap.foldWithKey (\x a rec -> do
                                   m <- rec
                                   a' <- map_type a
                                   return $ IMap.insert x a' m) (return IMap.empty) gamma_p

    -- Unify the flag constraints yet again
    fls <- unify_flags $ snd csett
    csett <- return (fst csett, fls)

    -- Last of the free variables of t - to be place after the unification, since
    -- the algorithm produces new variables that also have to be generic.
    endtype <- get_context >>= return . type_id
    endflag <- get_context >>= return . flag_id


    -- Generalize the types of the pattern (= polymorphism)
    gamma_p <- IMap.foldWithKey (\x a rec -> do
                                    ctx <- rec
                                    -- First apply the substitution
                                    a' <- map_type a

                                    -- Build the polymorphic type
                                    gena <- make_polymorphic_type a' csett (\f -> limflag <= f && f < endflag, \x -> limtype <= x && x < endtype)
                                    
                                    -- Update the typing context of u
                                    return $ IMap.insert x gena ctx) (return IMap.empty) gamma_p

    -- Type u - The constraints on the type of the let are transfered to the type of u
    csetu <- constraint_typing (gamma_p <+> gamma_u) u cst
    
    -- Generate the flag constraints for the intersection
    disunion <- return $ linear_union [fvt, fvu]
    (_, delta) <- sub_context disunion gamma
    duplicable_context delta
    
    return csetu

  -- If it is not a VALUE (for example a function application), it is given a simple type
  else do
    -- Type u - The constraints on the type of the let are transfered to the type of u
    csetu <- constraint_typing ((IMap.map typescheme_of_type gamma_p) <+> gamma_u) u cst
    
    -- Generate the flag constraints for the intersection
    disunion <- return $ linear_union [fvt, fvu]
    (_, delta) <- sub_context disunion gamma
    duplicable_context delta
    
    return $ csetu <> csett



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

constraint_typing gamma (EDatacon ref dcon e) cst = do
  -- Extent of the expression
  info <- return $ no_info { c_ref = ref }

  -- Retrieve the definition of the data constructor, and instantiate its typing scheme
  dtype <- datacon_type dcon
  (dtype', csetd) <- instantiate dtype

  case (dtype', e) of
    -- No argument given, the constructor is typed as is
    (TBang n _, Nothing) -> do
        -- The context must be duplicable
        duplicable_context gamma
        update_ref ref (\ri -> Just ri { r_type = dtype' })
        return $ ((dtype' <:: cst) & info) <> (csetd & info)

    -- One argument given, and the constructor requires one
    (TBang _ (TArrow t u@(TBang n _)), Just e) -> do
        -- Type the argument of the data constructor
        csete <- constraint_typing gamma e [t]
        update_ref ref (\ri -> Just ri { r_type = u })
        return $ ((u <:: cst) & info) <> csete <> (csetd & info)

    (TBang _ _, Just _) ->
        throw $ ProgramError "constraint_typing: ill-typed data constructor"

-- Match typing rule
--
--          G1, !ID |- t : !p(!nA + !m B)              [L1]
--            G2, !ID, x : !nA |- u : V                [L2]
--            G2, !ID, y : !mB |- v : V                [L3]
-- ---------------------------------------------------
--  G1, G2, !ID |- match t with (x -> u | y -> v) : V  [L1 u L2 u L3 u {1 <= I, p <= n, p <= m}]
--

constraint_typing gamma (EMatch _ e blist) cst = do
  -- Extract the free type variables of e and of the bindings
  fve <- return $ free_var e
  fvlist <- List.foldl (\rec (p, f) -> do
                          r <- rec
                          fv <- return $ free_var f \\ free_var p
                          return $ List.union fv r) (return []) blist

  -- Type each of the bindings
  (gamma_bl, _) <- sub_context fvlist gamma
  (alist, csetlist) <- List.foldr (\(p, f) rec -> do
                                     (ar, cset) <- rec
                                     -- Bind the pattern p
                                     (a, gamma_p, csetp) <- bind_pattern p

                                     -- p must have a non functional type
                                     ext <- get_location
                                     Monad.QpState.assert IsNotfun a no_info { c_ref = reference e }

                                     -- Type the associated expression, with the same constraints cst as the original expression
                                     -- Refer to the case of 'if' for more clarity.
                                     csetf <- constraint_typing ((IMap.map typescheme_of_type gamma_p) <+> gamma_bl) f cst

                                     -- The type of the expression e must be a subtype of the type of the pattern
                                     return $ (a:ar, csetp <> csetf <> cset)) (return ([], emptyset)) blist

  -- Type e as a subtype of all the pattern types
  (gamma_e, _) <- sub_context fve gamma
  csete <- constraint_typing gamma_e e alist

  -- Generate the flag constraints for the intersection
  disunion <- return $ linear_union [fve, fvlist]
  (_, delta) <- sub_context disunion gamma
  duplicable_context delta
  
  return $ csete <> csetlist


-- Typing rule (if)
--
--     G1, !ID |- e : bool                 [L]
--       G2, !ID |- f : T                  [L']
--       G2, !ID |- g : T                  [L'']
-- ---------------------------------------
--  G1, G2, !ID |- if e then f else g : T  [L u L' u L'' u {1 <= I}]
--
-- Same as pattern matchings (since it is only a special case with the type bool = True | False

constraint_typing gamma (EIf _ e f g) cst = do
  -- Extract the free variables of e, f and g
  fve <- return $ free_var e
  fvfg <- return $ List.union (free_var f) (free_var g)
  
  -- Filter on the free variables of e and type e: e must have the type bool
  -- The expected type !0 bool makes the least assumption about the type of e
  (gamma_e, _) <- sub_context fve gamma
  csete <- constraint_typing gamma_e e [TBang zero TBool]

  -- Filter on the free variables of f an g. f and g must have the same type as the whole expression, so they
  -- inherit the same constraints.
  (gamma_fg, _) <- sub_context fvfg gamma
  csetf <- constraint_typing gamma_fg f cst
  csetg <- constraint_typing gamma_fg g cst

  -- Generate the flag constraints for the context delta
  disunion <- return $ linear_union [fve, fvfg]
  (_, delta) <- sub_context disunion gamma
  duplicable_context delta
  
  return $ csete <> csetf <> csetg


-- No typing rule, but a constraint on the type of the expression, of the form
--      e <: T   <==>   type of e <: T
-- The translation of the constraint type has been delayed up until there
-- to be able to generalize over the free variables of this type in the let-polymorphism
constraint_typing gamma (EConstraint e (t, typs)) cst = do
  t' <- translate_unbound_type t $ empty_label { l_types = typs }
  csete <- constraint_typing gamma e (t':cst)
  return csete







-- | Duplicate the input linear type, replacing every type variable or flag reference
-- by a newly generated one.
duplicate_lintype :: LinType -> QpState LinType
duplicate_lintype TUnit = do
  return TUnit

duplicate_lintype (TArrow t u) = do
  t' <- duplicate_type t
  u' <- duplicate_type u
  return (TArrow t' u')

duplicate_lintype (TTensor tlist) = do
  tlist' <- List.foldr (\t rec -> do
                          rc <- rec
                          t' <- duplicate_type t
                          return (t':rc)) (return []) tlist
  return (TTensor tlist')

duplicate_lintype (TUser n args) = do
  args' <- List.foldr (\a rec -> do
                         rc <- rec
                         a' <- duplicate_type a
                         return (a':rc)) (return []) args
  return (TUser n args')

duplicate_lintype (TVar _) = do
  x <- fresh_type
  return (TVar x)

duplicate_lintype (TCirc t u) = do
  t' <- duplicate_type t
  u' <- duplicate_type u
  return (TCirc t' u')

-- Remaining cases: bool int qubit
duplicate_lintype typ = do
  return typ


-- | Duplicate the input type, replacing every type variable or flag reference
-- by a newly generated one.
duplicate_type :: Type -> QpState Type
duplicate_type (TBang _ t) = do
  n <- fresh_flag
  t' <- duplicate_lintype t
  return $ TBang n t'

-- | Create a duplicate version of a type, and map the argument type variable to it.
-- The first type is assumed to be of the form !^/n/ /x/, where /x/ is a type variable.
map_to_duplicate :: Variable -> LinType -> QpState LinType
map_to_duplicate x t = do
  t' <- duplicate_lintype t
  mapsto x t'
  return t'




-- | Unification algorithm. The boolean argument determines whether approximations are permitted or not. The poset is the partially ordered set of the variables, and
-- will help finding the youngest variables. It is assumed that the poset corresponds to the associated constraint set.
unify_with_poset :: Bool -> Poset -> ConstraintSet -> QpState ConstraintSet
unify_with_poset exact poset (lc, fc) = do
  -- Recursive check
  stop <- return $ null_poset poset
  
  if stop then
    return (lc, fc)
  
  else do
    -- Ask the poset for its youngest variables
    (cx, poset) <- youngest_variables poset

    -- Filter the constraints which have an element of cx as right or left hand side
    (lcx, non_lcx) <- return $ List.partition (\c -> case c of 
                                                       Sublintype (TVar x) _ _ -> List.elem x cx
                                                       Sublintype _ (TVar y) _ -> List.elem y cx
                                                       Sublintype _ _ _ -> throw $ ProgramError "unify_with_poset: non-atomic constraint"
                                                       Subtype _ _ _ -> throw $ ProgramError "unify_with_poset: Subtype"
        ) lc
    -- Log
    logx <- return $ List.foldl (\s c -> "(" ++ pprint c ++ ") " ++ s) "" lcx
    lognonx <- return $ List.foldl (\s c -> "(" ++ pprint c ++ ") " ++ s) "" non_lcx
    newlog 1 logx
    newlog 1 lognonx
                                           
    -- Filter the atomic constraints
    (atomx, natomx) <- return $ List.partition is_atomic lcx

    -- Check the next action
    case (atomx, natomx) of

      -- No semi-composite constraints: trivial solution with x1 = .. = xn (approx) or do nothing (exact),  unify the rest
      (atomx, []) -> do

          if not exact then do

            -- APPROXIMATION :
            -- Of all the variables, keep only one and replace the rest
            (xh:rest) <- return cx
            List.foldl (\rec x -> do 
                          rec
                          mapsto x $ TVar xh) (return ()) rest
            unify_with_poset exact poset (non_lcx, fc)

          else do

            -- EXACT :
            -- Unify the rest, and keep the atomic constraints untouched
            (non_lcx', fc') <- unify_with_poset exact poset (non_lcx, fc)
            return (non_lcx' ++ atomx, fc')

      -- Semi-composite constraints :
      (atomx, cset) -> do
          
          (ischain, sorted) <- return $ chain_constraints lcx
          if not exact && ischain then do

            -- APPROXIMATION :
            -- When all the constraints are chained as: T <: x1 <: .. <: xn <: U, make the approximation x1 = .. = xn = T, T <: U
            newlog 1 "APPROX: CHAINED"

            -- Get the left and right ends of the chain of constraints
            leftend <- case List.head sorted of
                         Sublintype t _ _ -> return $ t
                         Subtype _ _ _ -> throw $ ProgramError "unify_with_poset: Subtype"
            rightend <- case List.last sorted of
                          Sublintype _ t _ -> return t
                          Subtype _ _ _ -> throw $ ProgramError "unify_with_poset: Subtype"

            -- One of the ends must be composite
            case (leftend, rightend) of
              (TVar x, _) -> do
                  -- Map everything to the right end
                  List.foldl (\rec x -> do
                                rec
                                mapsto x rightend) (return ()) cx

                  -- Unify the rest
                  unify_with_poset False poset (non_lcx, fc)
                  
              (_, TVar x) -> do
                  -- Map everything to the left end
                  List.foldl (\rec x -> do
                                  rec
                                  mapsto x leftend) (return ()) cx

                  -- Unify the rest
                  unify_with_poset False poset (non_lcx, fc)

              _ -> do
                  -- Map everything to the left end
                  List.foldl (\rec x -> do
                                rec
                                mapsto x leftend) (return ()) cx

                  -- Add the constraint  leftend <: rightend
                  cset' <- break_composite True ([Sublintype leftend rightend no_info], [])
                  poset <- return $ register_constraints (fst cset') poset

                  -- Unify the rest
                  unify_with_poset False poset $ cset' <> (non_lcx, fc)

          else do

            -- EXACT SOLUTION :
            -- Select a composite type from the semi-composite constraints
            newlog 1 "EXACT"
            model <- case List.head cset of
                       Sublintype (TVar _) t _ -> return t
                       Sublintype t (TVar _) _ -> return t
                       Sublintype _ _ _ -> throw $ ProgramError "non-atomic contraint"
                       Subtype _ _ _ -> throw $ ProgramError "unify_with_poset: Subtype"
                        

            -- Map the youngest variables each to a new specimen of the model
            List.foldl (\rec x -> do
                          rec
                          _ <- map_to_duplicate x model
                          return ()) (return ()) cx

            -- Rewrite and reduce the atomic constraints
            atomx' <- List.foldl (\rec constraint -> do
                                    case constraint of
                                      Sublintype (TVar x) (TVar y) info -> do
                                        atom <- rec
                                        xt <- appmap x
                                        yt <- appmap y
                                        atom' <- break_composite True ([Sublintype xt yt info], [])
                                        return $ atom' <> atom
                                      _ -> throw $ ProgramError "unify_with_poset: bad constraint"
                                 ) (return emptyset) atomx

            -- Rewrite and reduce the semi composite constraints
            cset' <- List.foldl (\rec c -> do
                                   cs <- rec
                                   case c of
                                     Sublintype (TVar x) u info -> do
                                         xt <- appmap x
                                         cs' <- break_composite True ([Sublintype xt u info], [])
                                         return $ cs' <> cs

                                     Sublintype t (TVar y) info -> do
                                         yt <- appmap y
                                         cs' <- break_composite True ([Sublintype t yt info], [])
                                         return $ cs' <> cs

                                     Sublintype _ _ _ -> throw $ ProgramError "non-atomic contraint"
                                     Subtype _ _ _ -> throw $ ProgramError "unify_with_poset: Subtype"
                                )  (return emptyset) cset

            -- Register the relations defined by those new constraints
            poset <- return $ register_constraints (fst atomx' ++ fst cset') poset

            -- Unify the rest
            unify_with_poset exact poset $ atomx' <> cset' <> (non_lcx, fc)


            {-
            
            else do           
              newlog 0 "UNCHAINED"
              
              onesided <- return $ is_one_sided cset
              -- If all the constraints are one-sided, make the approximation: x1 = .. = xn
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


-- | Type unification. Apply the function 'unify_with_poset' to a poset freshly created with the constraints
-- of the provided set. The boolean flag is the same as the argument of 'unify_with_poset'.
unify_types :: Bool -> ConstraintSet -> QpState ConstraintSet
unify_types exact cset = do
  poset <- return $ register_constraints (fst cset) empty_poset
  unify_with_poset exact poset cset





-- | Part of the flag unification. Look for flag constraints of the form 1 <= /n/ or /n/ <= 0, and apply their consequences
-- to the involved references. The boolean in the return value is needed for the termination, and indicates whether changes have been made.
apply_flag_constraints :: [FlagConstraint] -> QpState (Bool, [FlagConstraint])
apply_flag_constraints [] = do
  return (False, [])

apply_flag_constraints (c:cc) = do
  case c of
    Le 1 0 info -> do
        throw_NonDuplicableError info

    Le n 0 info -> do
        unset_flag n info
        (_, cc') <- apply_flag_constraints cc
        return (True, cc')

    Le 1 m info -> do
        set_flag m info
        (_, cc') <- apply_flag_constraints cc
        return (True, cc')

    Le m n info -> do
        vm <- flag_value m
        vn <- flag_value n
        case (vm, vn) of
          (One, Zero) -> do
              case c_type info of
                Just a -> do
                    a0 <- return $ subs_flag m 0 a
                    a1 <- return $ subs_flag n 1 a
                    throw_TypingError a0 a1 info { c_actual = False, c_type = Nothing }

                Nothing ->
                    throw_NonDuplicableError info

          (Unknown, Zero) -> do
              unset_flag m info
              (_, cc') <- apply_flag_constraints cc
              return (True, cc')
 
          (One, Unknown) -> do
              set_flag n info
              (_, cc') <- apply_flag_constraints cc
              return (True, cc')

          (Unknown, Unknown) -> do
              -- With no information, the constraint is kept aside while the rest of the set is being solved,
              -- then added back to the result.
              (b, cc') <- apply_flag_constraints cc
              return (b, c:cc')

          -- The remaining cases correspond to trivial constraints that can be discarded.
          _ -> do
              apply_flag_constraints cc


-- | Apply the function 'apply_flag_constraints' recursively until the constraint set becomes stable.
apply_flag_constraints_rec :: [FlagConstraint] -> QpState [FlagConstraint]
apply_flag_constraints_rec cset = do
  (b, cset') <- apply_flag_constraints cset
  if not b then
    return cset'
  else
    apply_flag_constraints_rec cset'



-- | Flag unification. First filter out the trivial constraints, before \'applying\' the constraints of
-- the form 1 <= /n/, /n/ <= 0. At the end of the flag unification, only constraints of the form /n/ <= /m/ remain, where neither /n/ nor /m/ has a value.
unify_flags :: [FlagConstraint] -> QpState [FlagConstraint]
unify_flags fc = do

  -- Elimination of trivial constraints f <= 1 and 0 <= f, -1 <= f and f <= -1
  fc' <- return $ List.filter (\(Le m n _) -> m /= 0 && n /= 1 && m /= -1 && n /= -1) fc

  -- Application of the constraints 1 <= f and f <= 0
  fc'' <- apply_flag_constraints_rec fc'
  return fc''


-- | Whole unification. First apply the type unification, then the flag unification on the resulting flag constraints.
-- The boolean flag is passed as an argument to 'unify_flags'.
unify :: Bool -> ConstraintSet -> QpState ConstraintSet
unify exact (lc, fc) = do
  -- Before type unification : map the types and break the composite constraints
  lc <- List.foldl (\rec c -> do
                      lc <- rec
                      case c of
                        Sublintype a b info -> do
                            a' <- map_lintype a
                            b' <- map_lintype b
                            return $ (Sublintype a' b' info):lc
                        Subtype t u info -> do
                            t' <- map_type t
                            u' <- map_type u
                            return $ (Subtype t' u' info):lc) (return []) lc

  cset <- break_composite True (lc, fc)

  -- Type unification
  (lc', fc') <- unify_types exact cset

  -- Flag unification
  fc'' <- unify_flags fc'

  -- Result
  return (lc', fc'')
