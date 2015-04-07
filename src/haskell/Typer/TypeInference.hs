-- | This module implements the constraint typing algorithm and the unification algorithm.
module Typer.TypeInference where

import Prelude hiding (filter)

import Classes hiding ((\\))
import Utils
import qualified Options (exactUnification, displayToplevelTypes)

import Parsing.Location hiding (location)
import qualified Parsing.Syntax as S

import qualified Language.Constructor as Constructor (typ)

import Core.Syntax
import Core.Translate
import Core.Environment as Environment (empty)

import Typer.TypingContext as Context
import Typer.Ordering as Poset
import Typer.Subtyping

import Monad.Error
import Monad.Core as Core hiding (environment)
import Monad.Typer as Typer

import Data.List ((\\))
import qualified Data.List as List
import Data.Sequence as Seq hiding (filter)
import Data.Array as Array
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IntMap
import Data.IntSet as IntSet hiding (filter)

import Control.Monad.Trans
import Control.Monad.Trans.State


-- | Type a toplevel binding. Type annotations are added during the type inference, and the new
-- declarations are returned.
typeDeclaration :: ConstraintSet -> TypingContext -> Declaration -> Typer (Declaration, ConstraintSet, TypingContext)
-- Toplevel expressions.
typeDeclaration topcset gamma (DExpr info value) = do
  -- Free variables of the new expression.
  let fve = freevar value
  a @ (TypeAnnot n _) <- runCore newType
  -- ALL TOP-LEVEL EXPRESSIONS MUST BE DUPLICABLE.
  setFlag n $ fromSource a $ InExpr value
  -- Type e. The constraints from the context are added for the unification.
  (gammaE, _) <- subContext fve gamma
  (value, cset) <- constraintTyping gammaE value [a]
  cset <- breakConstraintSet cset
  cset <- unify $ cset <> topcset
  -- Resolve the constraints (BECAUSE MAP_TYPE CAN CHANGE THE FLAGS).
  fc <- unifyFlags $ flagConstraints cset
  let cset' = cset { flagConstraints = fc }
  -- Check the assertions made.
  checkAssertions
  -- Return the new declaration.
  return (DExpr info { typ = a } value, cset', gamma)

-- Toplevel bindings.
typeDeclaration topcset gamma (DLet info rec x value) = do
  let fve = freevar value
  (gammaE, _) <- subContext fve gamma
  -- Mark the limit free variables / bound variables used in the typing of t.
  limtype <- runCore freshType
  limflag <- runCore freshFlag
  -- Create the type of the pattern.
  (binder, a, gammaP, csetp) <- bindPattern $ PVar info x
  -- Type e with this type.
  (value, csete) <- case rec of
      -- Add the bindings of the pattern into gammaE.
      Recursive -> constraintTyping ((IntMap.map schemeOfType gammaP) <+> gammaE) value [a]
      -- If not recursive, do nothing.
      Nonrecursive -> constraintTyping gammaE value [a]
  -- Unify the constraints produced by the typing of e (exact unification).
  --cset <- breakConstraintSet (csetp <> csete)     -- Break the composite constraints.
  cset <- unify (csetp <> csete)                    -- Unify.
  -- Map the types of the pattern.
  gammaP <- IntMap.foldWithKey (\x a rec -> do
      map <- rec
      a' <- resolveType a
      return $ IntMap.insert x a' map) (return IntMap.empty) gammaP
  -- Unify the set again.
  fls <- unifyFlags $ flagConstraints cset
  cset <- return cset { flagConstraints = fls }
  -- Check the assertions.
  checkAssertions
  -- Last of the free variables of e - to be place after the unification, since the algorithm
  -- produces new variables that also have to be generic.
  endtype <- runCore freshType
  endflag <- runCore freshFlag
  -- -- POLYMORPHISM -- -- If the expression is a VALUE, it can have a generic type.
  (gammaP, cset) <- if isValue value then do
    -- Generalize the types of the pattern (= polymorphism).
    gammaP <- IntMap.foldWithKey (\x a rec -> do
        ctx <- rec
        a' <- resolveType a
        -- Clean the constraint set.
        gena <- makePolymorphicType a' cset (\f -> limflag <= f && f < endflag, \x -> limtype <= x && x < endtype)
        -- Update the typing context of u.
        return $ IntMap.insert x gena ctx
      ) (return IntMap.empty) gammaP
    return (gammaP, emptyset)
    -- If the expression is not a value, it has a classical type.
    else return (IntMap.map schemeOfType gammaP, cset)
  options <- runCore getOptions
  if Options.displayToplevelTypes options then
    -- Print the types of the pattern p
    IntMap.foldWithKey (\x a rec -> do
        rec
        nx <- runCore $ variableName x
        case a of
          TypeScheme _ _ _ a -> do
            pa <- printType a
            runCore $ lift $ putStrLn ("val " ++ nx ++ " : " ++ pa)
        return ()
      ) (return ()) gammaP
  else return ()
  return (DLet info { typ = a } rec x value, cset, IntMap.union gamma gammaP)


-- | Type a list of declarations. The constraint set and typing context are initially empty.
typeDeclarations :: [Declaration] -> Typer ([Declaration], TypingContext)
typeDeclarations declarations = do
  (declarations, cset, gamma) <- List.foldl (\rec decl -> do
      (declarations, cset, gamma) <- rec
      (decl, cset, gamma) <- typeDeclaration cset gamma decl
      return (decl:declarations, cset, gamma)
    ) (return ([], emptyset, IntMap.empty)) declarations
  -- All the variables that haven't been used must be duplicable.
  duplicableContext gamma
  _ <- unify cset
  return (declarations, gamma)


-- | Filter a set of flag constraints. This removes the trivial constraints (/n/ <= 1), (0 <= /n/),
-- (-1 <= /n/), (/n/ <= -1), and applies the constraints 1 <= /n/ (resp. /n/ <= 0) by setting the
-- flag /n/ to 1 (resp. 0).
filter :: [FlagConstraint] -> Typer [FlagConstraint]
filter fc = do
  List.foldl (\rec c -> do
      r <- rec
      case c of
        -- Useless.
        Le 0 _ _ -> return r
        Le _ 1 _ -> return r
        -- Direct.
        Le 1 n info -> do
          setFlag n info
          return r
        Le n 0 info -> do
          unsetFlag n info
          return r
        -- Everything else.
        _ -> return $ c:r
    ) (return []) fc


-- | Generalize a type, associated with constraints, over its free variables and flags. The free
-- variables of the type are those that are greater or equal to a limit type\/flag.
makePolymorphicType :: Type                                 -- ^ Generic type.
                    -> ConstraintSet                        -- ^ Unreduced constraint set.
                    -> (Flag -> Bool, Variable -> Bool)     -- ^ Define the scope of variables.
                    -> Typer TypeScheme
makePolymorphicType typ (ConstraintSet lc fc) (isref, isvar) = do
  let (ff, fv) = (freeflag typ, freevar typ)
  -- A variable / flag is to be kept (in the constraints) if it is from the context, or if it is in
  -- the final type.
  let (keepref, keepvar) = (
        \f -> (not $ isref f) || IntSet.member f ff,
        \v -> (not $ isvar v) || IntSet.member v fv)

  -- Walk starting from one point, stopping on the other important vertices.
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
            -- If the node is not important, map to the origin
            if not $ keep node then map node origin
            else return ()

            let next = case IntMap.lookup node g of
                  Nothing -> []
                  Just s -> s
            (nx, nc) <- List.foldl (\rec n -> do
                (nx, nc) <- rec
                -- Already treated, omit.
                if List.elem n visited then return (nx,nc)
                -- The vertex is important, write down the new constraint (origin, n).
                else if keep n then return (nx, (origin,n):nc)
                -- The vertex is not important, map it to the origin
                else do return (n:nx, nc)) (return ([],[])) next
            wnc <- walk origin (nx ++ rest) g (node:visited) keep map
            return $ nc ++ wnc

  -- Apply the walk function to all the important vertices.
  let walkAll = \vertices g keep map ->
        List.foldl (\rec ori -> do
            nc <- rec
            case IntMap.lookup ori g of
              Nothing -> return nc
              Just s -> do
                wnc <- walk ori s g [ori] keep map
                return $ wnc ++ nc
          ) (return []) vertices
   -- Flags.
  let g = List.foldl (\g (Le x y _) ->
        case IntMap.lookup x g of
          Just c -> IntMap.insert x (y:c) g
          Nothing -> IntMap.insert x [y] g
        ) IntMap.empty fc

  let initf = List.filter keepref $ IntMap.keys g
  cs <- walkAll initf g keepref (\_ _ -> return ())
  let fc' = List.map (\(n,m) -> Le n m noInfo) cs

  -- Types.
  let g = List.foldl (\g c ->
        case c of
          SubLinearType (TypeVar x) (TypeVar y) _ ->
            case IntMap.lookup x g of
              Just c -> IntMap.insert x (y:c) g
              Nothing -> IntMap.insert x [y] g
          _ -> throwNE $ ProgramError $ "TypeInference:makePolymorphicType: unexpected unreduced constraint " ++ (pprint c)
        ) IntMap.empty lc

  let initv = List.filter keepvar $ IntMap.keys g
  cs' <- walkAll initv g keepvar (\a b -> mapsto a (TypeVar $ IntSet.findMin fv))
  let lc' = List.map (\(n,m) -> SubLinearType (TypeVar n) (TypeVar m) noInfo) cs'

  -- Build the polymorphic type.
  let genfv = List.filter isvar $ IntSet.toList fv
      genff = List.filter isref $ IntSet.toList ff

  return $ TypeScheme genff genfv (ConstraintSet lc' fc') typ



-- | Build the constraint typing derivation. The algorithm inputs an incomplete constraint typing
-- judgment /G/ |- /t/ : /T/_1 .. /T/_/n/, and produces the constraint set /L/ such that the relation
-- /G/ |- /t/ : /T/_1 .. /T/_/n/ [/L/] holds. The list of types /T/_1 .. /T/_/n/ corresponds to a set
-- of upper bounds of the type of /t/. It is initially of size 1 and can be increased via the
-- expressions (/e/ <: /T/) imposing that the type of /e/ be a subtype of /T/. The constraint typing
-- relations are (case by case):
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
constraintTyping :: TypingContext -> Expr -> [Type] -> Typer (Expr, ConstraintSet)
-- | Constant typing rules.
--
-- --------------------
--  !I G  |- c : !n Tc  [{1 <= I}]
--
constraintTyping gamma (EConstant info c) cst = do
  -- The context must be duplicable.
  duplicableContext gamma
  -- Type the constant.
  let typ = case c of
        ConstInt _ -> int
        ConstBool _ -> bool
        ConstUnit -> unit
  let e = EConstant info { typ = typ } c
      i = fromSource typ $ InExpr e
  return (e, ConstraintSet ((typ <:: cst) & i) [])

-- | Axiom typing rules.
--
-- ---------------------
--  !IG, t : T |- t : U  [{T <: U, 1 <= I}]
--
constraintTyping gamma (EVar info x) cst = do
  -- Retrieve the type of x from the typing context.
  sa <- Context.typeOf x gamma
  (a, csetx) <- instantiate sa
  -- Have the rest of the context be duplicable.
  (_, gamma') <- subContext (IntSet.singleton x) gamma
  duplicableContext gamma'
  -- Information.
  let e = EVar info { typ = a } x
      i = fromSource a $ InExpr e
  return (e, (a <:: cst) & i <> csetx & i)

constraintTyping gamma (EGlobal info x) cst = do
  -- Retrieve the type of x from the typing context.
  sa <- Typer.typeOf x
  (a, csetx) <- instantiate sa
  -- Have the context be duplicable.
  duplicableContext gamma
  -- Information.
  let e = EGlobal info { typ = a } x
      i = fromSource a $ InExpr e
  return (e, (a <:: cst) & i <> csetx & i)

-- | Error typing rule. This rule ignores the context, and doesn't expect all the variables wihtin
-- to be duplicable.
constraintTyping gamma (EError msg) cst = do
  a <- runCore $ newType
  return (EError msg, (a <:: cst) <> emptyset)

-- | Box typing rule.
--
-- ------------------------------------------------------
--  !I G |- box[T] :  !n (!1 (T -> U) -> !n Circ (T, U))  [L u {1 <= I}]
--
constraintTyping gamma (EBox info a) cst = do
  -- The context must be duplicable.
  duplicableContext gamma
  -- Build the type of box.
  b <- runCore newType
  let typ = arrow (arrow0 a b) (circ a b)
  -- Information.
  let e = EBox info { typ = typ } a
      i = fromSource typ $ InExpr e
  return (e, ConstraintSet ((typ <:: cst) & i) [])

-- | Rev typing rule
--
-- --------------------------------------------
--  G |- rev : !n (!n Circ (T, U) -> !n Circ (U, T))  [L]
--
constraintTyping gamma (ERev info) cst = do
  -- The context must be duplicable.
  duplicableContext gamma
  -- Build the type of rev.
  a <- runCore newType
  b <- runCore newType
  let typ = arrow (circ0 a b) (circ b a)
  -- Information.
  let e = ERev info { typ = typ }
      i = fromSource typ $ InExpr e
  return (e, ConstraintSet ((typ <:: cst) & i) [])


-- | Unbox typing rule.
--
-- ------------------------------------------------
--  G |- unbox : !1 (!n circ(T, U) -> !1 (T -> U))  [L]
--
constraintTyping gamma (EUnbox info) cst = do
  -- The context must be duplicable.
  duplicableContext gamma
  -- Build the type of unbox.
  a <- runCore newType
  b <- runCore newType
  let typ = arrow (circ0 a b) (arrow a b)
  -- Information.
  let e = EUnbox info { typ = typ }
      i = fromSource typ $ InExpr e
  return (e, ConstraintSet ((typ <:: cst) & i) [])

-- App typing rule.
--
--  G1, !ID |- t : a -> T   [L]
--     G2, !ID |- u : a     [L']
-- ------------------------
--  G1, G2, !ID |- t u : T  [L u L' u {1 <= I}]
--
constraintTyping gamma (EApp t u) cst = do
  -- Create the type of the argument.
  a <- runCore newType
  -- Extract the free variables of t and u.
  let fvt = freevar t
      fvu = freevar u
  -- Filter on the free variables of t and type t. The constraints on the actual type of the
  -- application are transformed into constraints on the type of the function.
  (gammaT, _) <- subContext fvt gamma
  (t, csett) <- constraintTyping gammaT t (List.map (\t -> arrow0 a t) cst)
  -- Filter on the free variables of u and type u.
  (gammaU, _) <- subContext fvu gamma
  (u, csetu) <- constraintTyping gammaU u [a]
  -- Construction of the constraint for !I Delta, the intersection of Gt and Gu.
  let disunion = linearUnion [fvt, fvu]
  (_, delta) <- subContext disunion gamma
  duplicableContext delta
  -- Return the union of the two constraint sets.
  return (EApp t u, csetu <> csett)


-- Lambda typing rule.
--
--    !IG, x : a |- t : b     [L]
-- --------------------------
--  !IG |- \x.t : !n(a -> b)  [L u {n <= Ii}]
--
constraintTyping gamma (EFun info arg body) cst = do
  -- Detailed information on the type of the function.
  n <- runCore freshFlag
  -- Context annotations (without the pattern's bindings).
  let flags = contextAnnotation gamma
  -- Bind the argument in the current context - this returns the type a of the argument of the
  -- abstraction
  (arg, a, gammaA, csetArg) <- bindPattern arg
  b <- runCore newType
  -- Type the body.
  (body, csetBody) <- constraintTyping ((IntMap.map schemeOfType gammaA) <+> gamma) body [b]
  -- Build the context constraints: n <= I.
  fconstraints <- filter $ List.map (\(_, f) -> Le n f noInfo) flags
  -- Add information.
  let typ = apply n "->" [a, b]
      e = EFun info { typ = typ } arg body
      i = fromSource typ $ InExpr e
  return (e, csetArg <> csetBody <> ((typ <:: cst) & i) <> fconstraints)

-- Tensor intro typing rule.
--
--    G1, !ID |- t : !n a      [L]
--    G2, !ID |- u : !n b      [L']
-- ---------------------------
--  G1, G2, !ID |- <t, u> : T  [L u L' u {1 <= I} u {!n (a * b) <: T}]
--
constraintTyping gamma (ETuple info tuple) cst = do
  -- Build the type of the tensor.
  p <- runCore freshFlag
  ts <- List.foldr (\_ rec -> do
      ts <- rec
      t <- runCore newType
      return $ t:ts
    ) (return []) tuple
  -- Extract the free variables of all the inner expressions.
  fvlist <- List.foldr (\e rec -> do
      r <- rec
      return $ (freevar e):r
    ) (return []) tuple
  -- Type the inner expressions, and extract the constraints.
  (tuple, csetlist) <- List.foldr (\(e, t, fv) rec -> do
      (tuple, cset) <- rec
      (gammaE, _) <- subContext fv gamma
      (e, cset') <- constraintTyping gammaE e [t]
      return (e:tuple, cset <> cset')
    ) (return ([], emptyset)) $ List.zip3 tuple ts fvlist
  -- Add information.
  let typ = apply p "*" ts
      e = ETuple info { typ = typ } tuple
      i = fromSource typ $ InExpr e
  -- Construction of all the constraints p <= f1 ... p <= fn.
  pcons <- filter $ List.map (\(TypeAnnot n _) -> Le p n i) ts
  -- Construction of the constraints of delta.
  let disunion = linearUnion fvlist
  (_, delta) <- subContext disunion gamma
  duplicableContext delta
  -- Return.
  return (e, csetlist <> ((typ <:: cst) & i) <> pcons)

-- Tensor elim typing rule, generalized to work with any kind of pattern.
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
--  where A = free variables of T \\ freevariables of G1, !ID
--
constraintTyping gamma (ELet rec binder value body) cst = do
  -- Extract the free variables of t and u.
  let fvt = freevar value
      fvu = freevar body
  -- Give the corresponding sub contexts.
  (gammaT, _) <- subContext fvt gamma
  (gammaU, _) <- subContext fvu gamma
  -- Mark the limit free variables / bound variables used in the typing of t.
  limtype <- runCore freshType
  limflag <- runCore freshFlag
  -- Create the type of the binder pattern.
  (binder, a, gammaP, csetp) <- bindPattern binder
  -- Type the value with this type.
  (value, csett) <- case rec of
      -- Add the bindings of the pattern into gamma_fvt
      Recursive -> constraintTyping ((IntMap.map schemeOfType gammaP) <+> gammaT) value [a]
      -- If not recursive, do nothing.
      Nonrecursive -> constraintTyping gammaT value [a]

  -- -- POLYMORPHISM -- --
  -- If the expression is a VALUE, then the type can be generic.
  if isValue value then do
    -- Unify the constraints produced by the typing of t (exact unification).
    cs <- breakConstraintSet $ csetp <> csett       -- Break the composite constraints.
    csett <- unify cs                               -- Unify.
    -- Apply the substitution produced by the unification of csett to the context gammaU.
    gammaU <- IntMap.foldWithKey (\x a rec -> do
        map <- rec
        a' <- resolveScheme a
        return $ IntMap.insert x a' map
      ) (return IntMap.empty) gammaU
    -- Apply the substitution to the context gammaP
    gammaP <- IntMap.foldWithKey (\x a rec -> do
        map <- rec
        a' <- resolveType a
        return $ IntMap.insert x a' map
      ) (return IntMap.empty) gammaP
    -- Unify the flag constraints yet again.
    fls <- unifyFlags $ flagConstraints csett
    csett <- return csett { flagConstraints = fls }
    -- Last of the free variables of t - to be place after the unification, since the algorithm
    -- produces new variables that also have to be generic.
    endtype <- runCore freshType
    endflag <- runCore freshFlag
    -- Generalize the types of the pattern (= polymorphism).
    gammaP <- IntMap.foldWithKey (\x a rec -> do
        ctx <- rec
        -- First apply the substitution.
        a' <- resolveType a
        -- Build the polymorphic type.
        gena <- makePolymorphicType a' csett (\f -> limflag <= f && f < endflag, \x -> limtype <= x && x < endtype)
        -- Update the typing context of the body.
        return $ IntMap.insert x gena ctx
      ) (return IntMap.empty) gammaP

    -- Type the body - The constraints on the type of the let are transfered to the type of the body.
    (body, csetu) <- constraintTyping (gammaP <+> gammaU) body cst
    -- Generate the flag constraints for the intersection.
    let disunion = linearUnion [fvt, fvu]
    (_, delta) <- subContext disunion gamma
    duplicableContext delta
    -- Return only the constraints produced by the body.
    let e = ELet rec binder value body
    return (e, csetu)

  -- If it is not a VALUE (for example a function application), it is given a simple type
  else do
    -- Type u - The constraints on the type of the let are transfered to the type of the body.
    (body, csetu) <- constraintTyping ((IntMap.map schemeOfType gammaP) <+> gammaU) body cst
    -- Generate the flag constraints for the intersection.
    let disunion = linearUnion [fvt, fvu]
    (_, delta) <- subContext disunion gamma
    duplicableContext delta
    let e = ELet rec binder value body
    return (e, csetu <> csett)



-- Data constructor typing rule.
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

constraintTyping gamma (EDatacon info cons e) cst = do
  -- Retrieve the definition of the data constructor, and instantiate its typing scheme.
  def <- runCore $ getConstructorInfo cons
  (typ', cset) <- instantiate $ Constructor.typ def
  case (typ', e) of
    -- No argument given, the constructor is typed as is.
    (TypeAnnot _ _, Nothing) -> do
      -- The context must be duplicable.
      duplicableContext gamma
      let f = EDatacon info { typ = typ' } cons Nothing
          i = fromSource typ' $ InExpr f
      return (f, ((typ' <:: cst) <> cset) & i)
    -- One argument given, and the constructor requires one.
    (TypeAnnot _ (TypeApply _ [t, u]), Just e) -> do
      -- Type the argument of the data constructor
      (e, cset') <- constraintTyping gamma e [t]
      let f = EDatacon info { typ = typ' } cons $ Just e
          i = fromSource typ' $ InExpr f
      return (f, ((u <:: cst) & i) <> cset' <> (cset & i))
    -- Unexpected case.
    (TypeAnnot _ _, Just _) ->
        fail "TypeInference:constraintTyping: ill-typed data constructor"

-- Match typing rule.
--
--          G1, !ID |- t : !p(!nA + !m B)              [L1]
--            G2, !ID, x : !nA |- u : V                [L2]
--            G2, !ID, y : !mB |- v : V                [L3]
-- ---------------------------------------------------
--  G1, G2, !ID |- match t with (x -> u | y -> v) : V  [L1 u L2 u L3 u {1 <= I, p <= n, p <= m}]
--
constraintTyping gamma (EMatch info test cases) cst = do
  -- Extract the free type variables of the test and of the bindings.
  let fve = freevar test
      fvlist = IntSet.unions $ List.map (\(Binding p f) -> (freevar f) IntSet.\\ (freevar p)) cases
  -- Type each of the bindings.
  (gammaC, _) <- subContext fvlist gamma
  (cases, tlist, csetlist) <- List.foldr (\(Binding binder c) rec -> do
      (cases, tlist, cset) <- rec
      -- Bind the pattern.
      (binder, a, gammaP, csetp) <- bindPattern binder
      -- p must have a non functional type.
      assert IsNotfun a $ extent $ patternInfo binder
      -- Type the associated expression, with the same constraints cst as the original expression.
      -- Refer to the case of 'if' for more clarity.
      (c, csetc) <- constraintTyping ((IntMap.map schemeOfType gammaP) <+> gammaC) c cst
      -- The type of the expression e must be a subtype of the type of the pattern.
      return ((Binding binder c):cases, a:tlist, csetp <> csetc <> cset)
    ) (return ([], [], emptyset)) cases
  -- Type e as a subtype of all the pattern types.
  (gammaE, _) <- subContext fve gamma
  (test, csete) <- constraintTyping gammaE test tlist
  -- Generate the flag constraints for the intersection.
  let disunion = linearUnion [fve, fvlist]
  (_, delta) <- subContext disunion gamma
  duplicableContext delta
  -- Return.
  let e = EMatch info test cases
  return (e, csete <> csetlist)

-- Typing rule (if)
--
--     G1, !ID |- e : bool                 [L]
--       G2, !ID |- f : T                  [L']
--       G2, !ID |- g : T                  [L'']
-- ---------------------------------------
--  G1, G2, !ID |- if e then f else g : T  [L u L' u L'' u {1 <= I}]
--
-- Same as pattern matchings (since it is only a special case with the type bool = True | False
--
constraintTyping gamma (EIf e f g) cst = do
  -- Extract the free variables of e, f and g.
  let fve = freevar e
      fvfg = IntSet.union (freevar f) (freevar g)
  -- Filter on the free variables of e and type e: e must have the type bool. The expected type !0 bool
  -- makes the least assumption about the type of e.
  (gammaE, _) <- subContext fve gamma
  (e, csete) <- constraintTyping gammaE e [apply 0 "bool" []]
  -- Filter on the free variables of f an g. f and g must have the same type as the whole expression,
  -- so they inherit the same constraints.
  (gammaFG, _) <- subContext fvfg gamma
  (f, csetf) <- constraintTyping gammaFG f cst
  (g, csetg) <- constraintTyping gammaFG g cst
  -- Generate the flag constraints for the context delta.
  let disunion = linearUnion [fve, fvfg]
  (_, delta) <- subContext disunion gamma
  duplicableContext delta
  -- Return.
  return (EIf e f g, csete <> csetf <> csetg)

-- No typing rule, but a constraint on the type of the expression, of the form
--      e <: T   <==>   type of e <: T
-- The translation of the constraint type has been delayed up until there to be able to generalize
-- over the free variables of this type in the let-polymorphism.
constraintTyping gamma (ECoerce e (t, ctx)) cst = do
  let state = TranslateState {
        bound = False, location = unknownExtent,
        environment = Environment.empty,
        types = ctx, currentModule = ""
      }
  (t', _) <- runCore $ runStateT (translateUnboundType t) state
  constraintTyping gamma e (t':cst)



-- | Duplicate the input linear or simple type, replacing each type variable or flag reference by a
-- newly generated variable.
duplicateLinearType :: LinearType -> Typer LinearType
duplicateLinearType (TypeVar x) = do
  x' <- runCore freshType
  return $ TypeVar x'
-- The type constant does not need to be duplicated.
duplicateLinearType (TypeApply c args) = do
  args' <- List.foldl (\rec a -> do
      args <- rec
      a' <- duplicateType a
      return $ a':args
    ) (return []) args
  return $ TypeApply c args'

duplicateType :: Type -> Typer Type
duplicateType (TypeAnnot _ t) = do
  n <- runCore freshFlag
  t' <- duplicateLinearType t
  return $ TypeAnnot n t'


-- | Create a duplicate version of a type, and map the argument type variable to it. The first type
-- is assumed to be of the form !^/n/ /x/, where /x/ is a type variable.
mapToDuplicate :: Variable -> LinearType -> Typer LinearType
mapToDuplicate x t = do
  t' <- duplicateLinearType t
  mapsto x t'
  return t'


-- | Unification algorithm. The boolean argument determines whether approximations are permitted or not.
-- The poset is the partially ordered set of the variables, and will help finding the youngest variables.
-- It is assumed that the poset corresponds to the associated constraint set.
unifyWithPoset :: Bool -> ConstraintSet -> Poset ConstraintSet
unifyWithPoset exact (ConstraintSet lc fc) = do
  -- Recursive check.
  stop <- nullPoset
  if stop then return $ ConstraintSet lc fc
  else do
    -- Ask the poset for its youngest variables.
    cx <- youngestVariables
    -- Filter the constraints which have an element of cx as right or left hand side.
    let (lcx, nonlcx) = List.partition (\c -> case c of
          SubLinearType (TypeVar x) _ _ -> List.elem x cx
          SubLinearType _ (TypeVar y) _ -> List.elem y cx
          -- Non atomic constraints shouldn't exist here.
          _ -> throwNE $ ProgramError "TypeInference:unifyWithPoset: unexpected non-atomic constraint"
         ) lc
    -- Log.
    lift $ Typer.log 1 $ List.foldl (\s c -> "(" ++ pprint c ++ ") " ++ s) "" lcx
    lift $ Typer.log 1 $ List.foldl (\s c -> "(" ++ pprint c ++ ") " ++ s) "" nonlcx
    -- Filter the atomic constraints.
    let (atomx, natomx) = List.partition isAtomic lcx
    -- Check the next action.
    case (atomx, natomx) of
      -- No semi-composite constraints: trivial solution with x1 = .. = xn (approx) or do nothing
      -- (exact), unify the remaining constraints.
      (atomx, []) -> do
        if not exact then do
          -- APPROXIMATION : Of all the variables, keep only one and replace the rest.
          let (xh, rest) = case cx of [] -> (0, []) ; (xh:rest) -> (xh, rest)
          List.foldl (\rec x -> do
              rec
              lift $ mapsto x $ TypeVar xh) (return ()) rest
          unifyWithPoset exact $ ConstraintSet nonlcx fc
        else do
          -- EXACT : Unify the rest, and keep the atomic constraints untouched.
          (ConstraintSet nonlcx' fc') <- unifyWithPoset exact (ConstraintSet nonlcx fc)
          return $ ConstraintSet (nonlcx' ++ atomx) fc'

      -- Semi-composite constraints : try chaining the constraints in order to make approximations.
      -- If approximations are disabled, or if the constraints can't be chained, unify the constraints
      -- the usual way.
      (atomx, cset) -> do
        let (ischain, sorted) = chain_constraints lcx
        if not exact && ischain then do
          -- APPROXIMATION : When all the constraints are chained as: T <: x1 <: .. <: xn <: U, make
          -- the approximation x1 = .. = xn = T, T <: U.
          lift $ Typer.log 1 "APPROX: CHAINED"
          -- Get the left and right ends of the chain of constraints.
          let leftend = case List.head sorted of
                SubLinearType t _ _ -> t
                Subtype _ _ _ -> throwNE $ ProgramError "TypeInference:unifyWithPoset: unexpected type constraint"
          let rightend = case List.last sorted of
                SubLinearType _ t _ -> t
                Subtype _ _ _ -> throwNE $ ProgramError "TypeInference:unifyWithPoset: unexpected type constraint"
          -- One of the ends must be composite.
          case (leftend, rightend) of
            -- Map all the variables to the right end.
            (TypeVar x, _) -> do
              List.foldl (\rec x -> do
                  rec
                  lift $ mapsto x rightend) (return ()) cx
              -- Unify the rest.
              unifyWithPoset False $ ConstraintSet nonlcx fc
            -- Map all the variables to the left end.
            (_, TypeVar x) -> do
              List.foldl (\rec x -> do
                  rec
                  lift $ mapsto x leftend) (return ()) cx
              -- Unify the rest.
              unifyWithPoset False $ ConstraintSet nonlcx fc
            -- Map all the variables to the left end, and unify the rest, adding the constraint T <: U.
            _ -> do
              List.foldl (\rec x -> do
                  rec
                  lift $ mapsto x leftend) (return ()) cx
              -- Add the constraint  leftend <: rightend.
              cset' <- lift $ breakConstraint $ SubLinearType leftend rightend noInfo
              registerConstraints $ typeConstraints cset'
              -- Unify the rest.
              unifyWithPoset False $ cset' <> (ConstraintSet nonlcx fc)

        else do
          -- EXACT SOLUTION : Select a composite type from the semi-composite constraints.
          lift $ Typer.log 1 "EXACT"
          let model = case List.head cset of
                SubLinearType (TypeVar _) t _ -> t
                SubLinearType t (TypeVar _) _ -> t
                _ -> throwNE $ ProgramError "TypeInference:unifyWithPoset: unexpected non-atomic contraint"
          -- Map the youngest variables each to a new specimen of the model.
          List.foldl (\rec x -> do
                rec
                _ <- lift $ mapToDuplicate x model
                return ()) (return ()) cx
          -- Rewrite and reduce the atomic constraints.
          atomx' <- List.foldl (\rec constraint -> do
              case constraint of
                SubLinearType (TypeVar x) (TypeVar y) info -> do
                  atom <- rec
                  xt <- lift $ resolveVar x
                  yt <- lift $ resolveVar y
                  atom' <- lift $ breakConstraint $ SubLinearType xt yt info
                  return $ atom' <> atom
                _ -> fail "TypeInference:unifyWithPoset: unexpected non-atomic constraint"
            ) (return emptyset) atomx
          -- Rewrite and reduce the semi composite constraints.
          cset' <- List.foldl (\rec c -> do
              cset <- rec
              case c of
                SubLinearType (TypeVar x) u info -> do
                  xt <- lift $ resolveVar x
                  cset' <- lift $ breakConstraint $ SubLinearType xt u info
                  return $ cset' <> cset

                SubLinearType t (TypeVar y) info -> do
                  yt <- lift $ resolveVar y
                  cset' <- lift $ breakConstraint $ SubLinearType t yt info
                  return $ cset' <> cset

                _ -> fail "TypeInference:unifyWithPoset: unexpected non-atomic contraint"
            )  (return emptyset) cset
          -- Register the relations defined by those new constraints.
          registerConstraints $ (typeConstraints atomx') ++ (typeConstraints cset')
          -- Unify the rest.
          unifyWithPoset exact $ atomx' <> cset' <> (ConstraintSet nonlcx fc)


-- | Type unification. Apply the function 'unifyWithPoset' to a poset freshly created with the
-- constraints of the provided set. The boolean flag is the same as the argument of 'unifyWithPoset'.
unifyTypes :: Bool -> ConstraintSet -> Typer ConstraintSet
unifyTypes exact cset = do
  -- Computation in the poset monad.
  let computation = do
        registerConstraints $ typeConstraints cset
        unifyWithPoset exact cset
  (cset, _) <- runStateT computation Poset.empty
  return cset


-- | Part of the flag unification. Look for flag constraints of the form 1 <= /n/ or /n/ <= 0, and
-- apply their consequences to the involved references. The boolean in the return value is needed
-- for the termination, and indicates whether changes have been made.
applyFlagConstraints :: [FlagConstraint] -> Typer (Bool, [FlagConstraint])
applyFlagConstraints [] = return (False, [])
applyFlagConstraints (c:cc) = do
  case c of
    Le 1 0 info -> throwNonDuplicableError info
    Le n 0 info -> do
      unsetFlag n info
      (_, cc') <- applyFlagConstraints cc
      return (True, cc')
    Le 1 m info -> do
      setFlag m info
      (_, cc') <- applyFlagConstraints cc
      return (True, cc')
    Le m n info -> do
      vm <- getFlagValue m
      vn <- getFlagValue n
      case (vm, vn) of
        (One, Zero) -> do
          case sourceType info of
            Just a -> do
              let a0 = subs m (0 :: Variable) a
                  a1 = subs n (1 :: Variable) a
              throwTypingError a0 a1 info { actual = False, sourceType = Nothing }

            Nothing ->
              throwNonDuplicableError info

        (Unknown, Zero) -> do
          unsetFlag m info
          (_, cc') <- applyFlagConstraints cc
          return (True, cc')

        (One, Unknown) -> do
          setFlag n info
          (_, cc') <- applyFlagConstraints cc
          return (True, cc')

        (Unknown, Unknown) -> do
          -- With no information, the constraint is kept aside while the rest of the set is being
          -- solved, then added back to the result.
          (b, cc') <- applyFlagConstraints cc
          return (b, c:cc')

        -- The remaining cases correspond to trivial constraints that can be discarded.
        _ -> applyFlagConstraints cc


-- | Apply the function 'applyFlagConstraints' recursively until the constraint set becomes stable.
applyFlagConstraintsRec :: [FlagConstraint] -> Typer [FlagConstraint]
applyFlagConstraintsRec cset = do
  (b, cset') <- applyFlagConstraints cset
  if not b then return cset'
  else applyFlagConstraintsRec cset'


-- | Flag unification. First filter out the trivial constraints, before \'applying\' the constraints
-- of the form 1 <= /n/, /n/ <= 0. At the end of the flag unification, only constraints of the form
-- /n/ <= /m/ remain, where neither /n/ nor /m/ has a value.
unifyFlags :: [FlagConstraint] -> Typer [FlagConstraint]
unifyFlags fc = do
  -- Elimination of trivial constraints f <= 1 and 0 <= f, -1 <= f and f <= -1.
  let fc' = List.filter (\(Le m n _) -> m /= 0 && n /= 1 && m /= -1 && n /= -1) fc
  -- Application of the constraints 1 <= f and f <= 0.
  applyFlagConstraintsRec fc'


-- | Whole unification. First apply the type unification, then the flag unification on the resulting
-- flag constraints. The boolean flag is passed as an argument to 'unifyFlags'.
unify :: ConstraintSet -> Typer ConstraintSet
unify (ConstraintSet lc fc) = do
  options <- runCore getOptions
  -- Before type unification : map the types and break the composite constraints.
  lc <- List.foldl (\rec c -> do
    lc <- rec
    case c of
      SubLinearType a b info -> do
        a' <- resolveLinearType a
        b' <- resolveLinearType b
        return $ (SubLinearType a' b' info):lc
      Subtype t u info -> do
        t' <- resolveType t
        u' <- resolveType u
        return $ (Subtype t' u' info):lc) (return []) lc
  cset <- breakConstraintSet $ ConstraintSet lc fc
  -- Type unification.
  (ConstraintSet lc' fc') <- unifyTypes (Options.exactUnification options) cset
  -- Flag unification
  fc'' <- unifyFlags fc'
  -- Result
  return $ ConstraintSet lc' fc''
