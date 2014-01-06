-- | This module processes the surface syntax and translates it into the internal syntax. This includes: processing of type definitions, with inference of
-- the type properties (subtyping, qdata type); translation of the body (with scope analysis, generation of the export list, linking with the interface); some
-- functions to convert the syntax to raw Proto-Quipper code.
--
-- The subtyping constraints {user /a/ <: user /a/'} can't be interpreted as just {/a/ <: /a/'}. Indeed, the order of the
-- constraints may be reversed, as is the case with the type:
--
-- @
-- type foo a b =
--   Bar of a -> b
-- @
--
-- Intuitively, a constraint {foo /a/ /b/ <: foo /a/' /b/'} is to be reduced as {/a/' <: /a/, /b/ <: /b/'}, which would
-- correspond to the subtyping relation rule:
--
-- @
--   a' <: a          b <: b'
--   -----------------------
--     foo a b <: foo a' b'
-- @
--
-- One option would be to ask for the user to manually enter these subtyping relation rules.
-- Another option is to infer them automatically. This last option has been chosen, with the following
-- (unproved) inference algorithm.
--
-- Since algebraic types correspond to sum types (with induction), the natural way to obtain a subtyping relation
-- rule is to take the set of subtyping relations on the types of the data constructors:
-- given the type \"either\":
--
-- @
--  type either a b =
--    Left a
--  | Right b
-- @
--
-- the relation is, as inferred:
--
-- @
--    a <: a'          b <: b'
--   --------------------------
--   either a b <: either a' b'
-- @
--
-- and this corresponds to the natural definition. However, when the type is inductive,
-- as is the case of list, this would give:
--
-- @
--   a <: a'    list a <: list a'
--   ---------------------------
--        list a  <: list a'
-- @
--
-- This is not quite what we wanted, since the goal was to eliminate the composite constraints.
-- However, two remarks can be made:
--
-- * After reduction of the constraints, only atomic constraints on the type arguments remain.
--
-- * The number of possible constraints of this kind is limited: at most 2/n/ can exist, where /n/ is the number of type arguments.
--
-- Thus the idea of the subtyping inference algorithm: to \'unfold\' the subtyping constraints on algebraic types base on the unfolded definition
-- of the types until the set of atomic constraints stabilizes. This would give for the type list:
--
-- @
--        a <: a'
--   -----------------
--   list a <: list a'
-- @
--
-- which is the expected subtyping relation rule. This algorithm has yet to be proved correct.
module Core.Translate (
  translate_type,
  translate_bound_type,
  translate_unbound_type,
  translate_expression,
  translate_pattern,
  import_typedefs,
  import_typesyn) where

import Utils
import Classes
import Builtins

import Core.Syntax
import Core.LabellingContext (LabellingContext, empty_label, LVariable (..))
import qualified Core.LabellingContext as L
import Core.Printer

import Parsing.Location
import qualified Parsing.Syntax as S
import Parsing.Printer

import Interpret.Values
import Interpret.Circuits as C

import qualified Compiler.SimplSyntax as CS
import Compiler.Preliminaries (choose_implementation)

import Monad.QuipperError
import Monad.QpState
import Monad.Modules (Module)
import qualified Monad.Modules as M

import Data.Map as Map
import qualified Data.List as List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap



-- | From a given type written in the parsing syntax, produce a map that associates each free
-- variable with its variance.
variance :: Variance                        -- ^ The variance of the current type.
         -> S.Type                          -- ^ The type to check.
         -> [S.Type]                        -- ^ The type arguments.
         -> Map String Type                 -- ^ A partial labelling context.
         -> QpState (Map String Variance)   -- ^ The resulting map.
variance var (S.TVar a) [] typs = do
  -- The variance of a variance is the global variance.
  return $ Map.singleton a var
variance var (S.TVar a) arg typs = do
  -- The variance of each of the type arguments depends upon the variance imposed by the type.
  vars <- case Map.lookup a typs of
        Just (TBang _ (TAlgebraic id _)) ->
            algebraic_def id >>= return . arguments
        Just (TBang _ (TSynonym id _)) ->
            synonym_def id >>= return . arguments
        _ ->
            fail "Translate:variance: undefined type"
  List.foldl (\rec (vara, a) -> do
        m <- rec
        let var' = case vara of
              Unrelated -> Unrelated
              Equal -> Equal
              Covariant -> var
              Contravariant -> opposite var
        va <- variance var' a [] typs
        return $ Map.unionWith join va m
      ) (return Map.empty) $ List.zip vars arg
variance var (S.TTensor tlist) [] typs =
  -- The variance is unchanged.
  List.foldl (\rec a -> do
        m <- rec
        va <- variance var a [] typs
        return $ Map.unionWith join va m) (return Map.empty) tlist
variance var (S.TBang t) [] typs =
  -- The variance is unchanged.
  variance var t [] typs
variance var (S.TCirc t u) [] typs = do
  -- The argument has its variance reversed, the other has the same variance.
  vt <- variance (opposite var) t [] typs
  vu <- variance var u [] typs
  return $ Map.unionWith join vt vu
variance var (S.TArrow t u) [] typs = do
  -- The argument has its variance reversed, the other has the same variance.
  vt <- variance (opposite var) t [] typs
  vu <- variance var u [] typs
  return $ Map.unionWith join vt vu
variance var (S.TApp t u) arg typs =
  -- Nothing to do.
  variance var t (u:arg) typs
variance var (S.TLocated t _) arg typs =
  -- Nothing to do.
  variance var t arg typs
variance _ _ _ _ = do
  -- Other types, with no type variables.
  return Map.empty




-- | Import the type definitions in the current state.
-- The data constructors are labelled during this operation, their associated type translated, and themselves included in the field datacons of the state.
import_typedefs :: [S.Algdef]                 -- ^ A block of co-inductive type definitions.
                -> LabellingContext           -- ^ The current labelling context.
                -> QpState LabellingContext   -- ^ The updated labelling context.
import_typedefs dblock label = do
  -- Initialize the type definitions.
  typs <- List.foldl (\rec def@(S.Typedef typename args _) -> do
        typs <- rec
        let spec = Typedef {
          arguments = List.map (const Unrelated) args,     -- All type arguments are by default unrelated.
          definition = ([], [])
        }

        -- Register the type in the current context.
        id <- register_algebraic typename spec
        -- Add the type to the labelling context.
        return $ Map.insert typename (TBang 0 $ TAlgebraic id []) typs
      ) (return (L.types label)) dblock

  -- Build the unfolded type definition.
  constructors <- List.foldl (\rec (S.Typedef typename args dlist) -> do
        lbl <- rec
        -- Type id needed for updates.
        id <- case Map.lookup typename typs of
            Just (TBang _ (TAlgebraic id _)) -> return id
            _ -> fail "TransSyntax:import_typedefs: unexpected non-algebraic type"

        -- Bind the arguments of the type.
        -- For each string argument a, a type !n a is created and bound in the map mapargs.
        (args, mapargs) <- List.foldr (\x rec -> do
              (as, map) <- rec
              a <- new_type
              return (a:as, Map.insert x a map)) (return ([], typs)) args

        -- Translate the type of the data constructors.
        (dtypes, lbl) <- List.foldl (\rec (tag, (dcon, dtype)) -> do
              (dtyps, lbl) <- rec
              m <- fresh_flag
              (dtyp, argtyp, cset) <- case dtype of
                    -- If the constructor takes no argument
                    Nothing -> do
                        return (TBang m (TAlgebraic id args), Nothing, emptyset)
                    -- If the constructor takes one argument
                    Just dt -> do
                        dt@(TBang n _) <- translate_bound_type dt empty_label { L.types = mapargs }
                        return (TBang one $ TArrow dt $ TBang m $ TAlgebraic id args, Just dt, ([], [Le m n no_info]))

              -- Generalize the type of the constructor over the free variables and flags
              -- Those variables must also respect the constraints from the construction of the type.
              let (fv, ff) = (free_typ_var dtyp, free_flag dtyp)
              dtyp <- return $ TForall ff fv cset dtyp

              -- Register the datacon.
              id <- register_datacon dcon Datacondef {
                dtype = dtyp,
                datatype = id,
                tag = tag,
                implementation = -1,
                construct = Left CS.EUnit,
                deconstruct = \x -> CS.EVar x
              }
              return $ ((id, argtyp):dtyps, Map.insert dcon id lbl)) (return ([], lbl)) (List.zip [0..(List.length dlist)-1] dlist)

        -- Update the specification of the type.
        update_algebraic id $ \algdef -> Just $ algdef { definition = (args, dtypes) }

        return lbl) (return $ L.datacons label) dblock


  -- Update the variance of the type arguments of a single type.
  let update_variance typ = do
        let id = case Map.lookup (S.name typ) typs of
              Just (TBang _ (TAlgebraic id _)) -> id
              _ -> throwNE $ ProgramError "Translate:update_variance: undefined algebraic type"
        algdef <- algebraic_def id
        let old = arguments algdef
        upd <- variance Covariant (S.TTensor $ List.map (\(_,t) -> case t of { Nothing -> S.TUnit ; Just t -> t }) (S.definition typ)) [] typs
        let new = List.map (\a -> case Map.lookup a upd of { Nothing -> Unrelated ; Just var -> var }) $ S.arguments typ
        update_algebraic id $ \alg -> Just $ alg { arguments = new }
        return $ old == new

  -- Apply the function update_variance to a group of type definitions.
  let update_variances dblock = do
        end <- List.foldl (\rec typ -> do
              end <- rec
              upd <- update_variance typ
              return $ end && upd) (return True) dblock
        if end then
          return ()
        else
          update_variances dblock

  -- Print the information relevant to a type (constructors, ...).
  let print_info typ = do
        let id = case Map.lookup (S.name typ) typs of
              Just (TBang _ (TAlgebraic id _)) -> id
              _ -> throwNE $ ProgramError "Translate:update_variance: undefined algebraic type"
        algdef <- algebraic_def id
        newlog 0 $ List.foldl (\s (var, a) -> s ++ " " ++ show var ++ a) ("alg: " ++ S.name typ) $ List.zip (arguments algdef) (S.arguments typ)

  -- Compilation specifics.
  List.foldl (\rec alg -> do
        rec
        case Map.lookup (S.name alg) typs of
          Just (TBang _ (TAlgebraic id _)) -> choose_implementation id
          _ -> throwNE $ ProgramError "Translate:update_variance: undefined algebraic type"
      ) (return ()) dblock

  -- Apply the function update_variances
  update_variances dblock

  -- Print some information about the inferred variance
  List.foldl (\rec typ -> rec >> print_info typ) (return ()) dblock

  -- Return the updated labelling map for types, and the map for dataconstructors.
  return $ label { L.datacons = constructors,
                   L.types = typs }





-- | Translate and import a type synonym.
import_typesyn :: S.Syndef                    -- ^ A type synonym.
               -> LabellingContext            -- ^ The current labelling context.
               -> QpState LabellingContext    -- ^ The updated labelling context.
import_typesyn typesyn label = do
  -- Bind the arguments to core types.
  as <- new_types $ List.length (S.arguments typesyn)
  let margs = Map.fromList $ List.zip (S.arguments typesyn) as

  -- Translate the synonym type.
  syn <- translate_bound_type (S.definition typesyn) (label { L.types = Map.union margs $ L.types label })

  -- Determine the variance of each argument.
  var <- variance Covariant (S.definition typesyn) [] (L.types label)
  let arg = List.map (\a -> case Map.lookup a var of { Nothing -> Unrelated ; Just v -> v }) $ S.arguments typesyn

  -- Print it.
  newlog 0 (List.foldl (\s (var, a) -> s ++ " " ++ show var ++ a) ("syn: " ++ S.name typesyn) $ List.zip arg (S.arguments typesyn))

  -- Build the type specification
  spec <- return $ Typedef {
        arguments = arg,
        definition = (as, syn) }

  -- Register the type synonym
  id <- register_synonym (S.name typesyn) spec

  -- Add the type to the labelling context and return
  return label { L.types = Map.insert (S.name typesyn) (TBang 0 $ TSynonym id []) $ L.types label }





-- | Translate a type, given a labelling.
-- The output includes a set of structural constraints: e.g., !^p (!^n a * !^m b) imposes p <= n and p <= m.
translate_type :: S.Type
               -> [Type]                  -- ^ List of type arguments. Only when the type is algebraic may this list not be empty.
               -> (Map String Type, Bool) -- ^ A map of bound type variables. The boolean flag indicates how to deal with unbound variables:
                                          -- they can either:
                                          --
                                          -- * generate a typing error (the definition of algebraic types doesn't allow for unbound variables).
                                          --
                                          -- * be bound in the map (all other cases).
               -> QpState (Type, Map String Type)
translate_type S.TUnit [] m = do
  return (TBang one TUnit, fst m)

translate_type S.TBool [] m = do
  return (TBang one TBool, fst m)

translate_type S.TInt [] m = do
  return (TBang one TInt, fst m)

translate_type S.TQubit [] m = do
  return (TBang zero TQubit, fst m)

translate_type (S.TVar x) arg (label, bound) = do
  case Map.lookup x label of

    -- The variable is an algebraic type.
    Just (TBang _ (TAlgebraic id as)) -> do
        spec <- algebraic_def id
        let nexp = List.length $ arguments spec
            nact = List.length as + List.length arg

        if nexp == nact then do
          n <- fresh_flag
          return (TBang n $ TAlgebraic id (as ++ arg), label)
        else do
          ex <- get_location
          throwQ (WrongTypeArguments x nexp nact) ex

    -- The variable is a type synonym.
    Just (TBang _ (TSynonym id as)) -> do
        spec <- synonym_def id
        let nexp = List.length $ arguments spec
        let nact = List.length as + List.length arg

        if nexp == nact then do
          n <- fresh_flag
          return (TBang n $ TSynonym id (as ++ arg), label)
        else do
          ex <- get_location
          throwQ (WrongTypeArguments x nexp nact) ex


    -- The variable is just a bound type.
    Just typ ->
        if arg == [] then
          return (typ, label)
        else do
          ex <- get_location
          throwQ (WrongTypeArguments (pprint typ) 0 (List.length arg)) ex

    -- If the variable is not found, it can be a free variable (depending on the boolean arg)
    Nothing -> do
        if bound then do
          -- If the type variables are supposed to be bound, this one isn't.
          ex <- get_location
          throwQ (UnboundVariable x) ex

        else do
          -- Last case, if the type authorize free variables, register this one with a new type
          t <- new_type
          return (t, Map.insert x t label)

translate_type (S.TQualified m x) arg lbl = do
  typ <- lookup_qualified_type (m, x)

  -- Expected number of arguments
  nexp <- case typ of
        TBang _ (TAlgebraic alg _) -> do
          dalg <- algebraic_def alg
          return $ List.length $ arguments dalg
        TBang _ (TSynonym syn _) -> do
          dsyn <- synonym_def syn
          return $ List.length $ arguments dsyn
        _ -> fail $ "TransSyntax:translate_type: unexpected type in module interface: " ++ pprint typ

  -- Actual number
  nact <- return $ List.length arg

  if nexp == nact then do
    n <- fresh_flag
    case typ of
      TBang _ (TAlgebraic alg _) -> return (TBang n (TAlgebraic alg arg), fst lbl)
      TBang _ (TSynonym syn _) -> return (TBang n (TSynonym syn arg), fst lbl)
      _ -> fail $ "TransSyntax:translate_type: unexpected type in module interface: " ++ pprint typ
  else do
    ex <- get_location
    throwQ (WrongTypeArguments x nexp nact) ex

translate_type (S.TArrow t u) [] (label, bound) = do
  (t', lblt) <- translate_type t [] (label, bound)
  (u', lblu) <- translate_type u [] (lblt, bound)
  n <- fresh_flag
  return (TBang n (TArrow t' u'), lblu)

translate_type (S.TTensor tlist) [] (label, bound) = do
  n <- fresh_flag
  (tlist', lbl) <- List.foldr (\t rec -> do
                                 (r, lbl) <- rec
                                 (t', lbl') <- translate_type t [] (lbl, bound)
                                 return (t':r, lbl')) (return ([], label)) tlist
  return (TBang n (TTensor tlist'), lbl)

translate_type (S.TBang t) [] label = do
  (TBang _ t, lbl) <- translate_type t [] label
  return (TBang 1 t, lbl)

translate_type (S.TCirc t u) [] (label, bound) = do
  (t', lblt) <- translate_type t [] (label, bound)
  (u', lblu) <- translate_type u [] (lblt, bound)
  return (TBang one (TCirc t' u'), lblu)

-- Case of type application: the argument is pushed onto the arg list
translate_type (S.TApp t u) args (label, bound) = do
  (u', lblt) <- translate_type u [] (label, bound)
  (t', lblu) <- translate_type t (u':args) (lblt, bound)
  return (t', lblu)

translate_type (S.TLocated t ex) args label = do
  set_location ex
  translate_type t args label

translate_type (S.TForall a typ) [] (label, bound) = do
  a' <- new_type
  label' <- return $ Map.insert a a' label
  translate_type typ [] (label', bound)

-- Remaining cases: of types applied to an argument when they are not generic
translate_type t args label = do
  ex <- get_location
  throwQ (WrongTypeArguments (pprint t) 0 (List.length args)) ex



-- | Apply the function 'Typing.TransSyntax.translate_type' to a bound type.
-- The arguments must be null initially.
translate_bound_type :: S.Type -> LabellingContext -> QpState Type
translate_bound_type t label = do
  (t', _) <- translate_type t [] (L.types label, True)
  return t'



-- | Apply the function 'Typing.TransSyntax.translate_type' to unbound types.
-- The binding map is initially empty, and is dropped after the translation of the type.
-- No argument is passed to the top type.
translate_unbound_type :: S.Type -> LabellingContext -> QpState Type
translate_unbound_type t label = do
  (t', _) <- translate_type t [] (L.types label, False)
  return t'



-- | Translate a pattern, given a labelling map.
-- The map is updated as variables are bound in the pattern.
translate_pattern :: S.XExpr -> LabellingContext -> QpState (Pattern, Map String LVariable)
translate_pattern S.EUnit label = do
  ref <- create_ref
  update_ref ref (\ri -> Just ri { expression = Right $ PUnit ref })
  return (PUnit ref, L.variables label)

translate_pattern (S.EBool b) label = do
  ref <- create_ref
  update_ref ref (\ri -> Just ri { expression = Right $ PBool ref b })
  return (PBool ref b, L.variables label)

translate_pattern (S.EInt n) label = do
  ref <- create_ref
  update_ref ref (\ri -> Just ri { expression = Right $ PInt ref n })
  return (PInt ref n, L.variables label)

translate_pattern S.EWildcard label = do
  ref <- create_ref
  update_ref ref (\ri -> Just ri { expression = Right $ PWildcard ref })
  return (PWildcard ref, L.variables label)

translate_pattern (S.EVar x) label = do
  ref <- create_ref
  mod <- current_module
  id <- register_var mod x ref
  update_ref ref (\ri -> Just ri { expression = Right $ PVar ref id })
  return (PVar ref id, Map.insert x (LVar id) $ L.variables label)

translate_pattern (S.ETuple plist) label = do
  ref <- create_ref
  (plist', lbl) <- List.foldr (\p rec -> do
        (ps, lbl) <- rec
        (p', lbl') <- translate_pattern p label { L.variables = lbl }
        return ((p':ps), lbl')) (return ([], L.variables label)) plist
  update_ref ref (\ri -> Just ri { expression = Right $ PTuple ref plist' })
  return (PTuple ref plist', lbl)

translate_pattern (S.EDatacon datacon p) label = do
  ref <- create_ref
  case Map.lookup datacon $ L.datacons label of
    Just id -> do
        case p of
          Just p -> do
              (p', lbl) <- translate_pattern p label
              update_ref ref (\ri -> Just ri { expression = Right $ PDatacon ref id (Just p') })
              return (PDatacon ref id (Just p'), lbl)

          Nothing -> do
              update_ref ref (\ri -> Just ri { expression = Right $ PDatacon ref id Nothing })
              return (PDatacon ref id Nothing, L.variables label)

    Nothing ->
        throw_UnboundDatacon datacon

translate_pattern (S.ELocated p ex) label = do
  set_location ex
  translate_pattern p label

translate_pattern (S.EConstraint p t) label = do
  (p', lbl) <- translate_pattern p label
  return (PConstraint p' (t, L.types label), lbl)

translate_pattern (S.EApp (S.ELocated (S.EDatacon e Nothing) ex) f) label =
  translate_pattern (S.ELocated (S.EDatacon e $ Just f) ex) label

translate_pattern p _ = do
  ref <- get_location
  throwQ (ParsingError (pprint p)) ref


-- | Translate an expression, given a labelling map.
translate_expression :: S.XExpr -> LabellingContext -> QpState Expr
translate_expression S.EUnit _ = do
  ref <- create_ref
  update_ref ref (\ri -> Just ri { expression = Left $ EUnit ref })
  return (EUnit ref)

translate_expression (S.EBool b) _ = do
  ref <- create_ref
  update_ref ref (\ri -> Just ri { expression = Left $ EBool ref b })
  return (EBool ref b)

translate_expression (S.EInt n) _ = do
  ref <- create_ref
  update_ref ref (\ri -> Just ri { expression = Left $ EInt ref n })
  return (EInt ref n)

translate_expression (S.EVar x) label = do
  ref <- create_ref
  case Map.lookup x $ L.variables label of
    Just (LVar v) -> do
        update_ref ref (\ri -> Just ri { expression = Left $ EVar ref v })
        return (EVar ref v)

    Just (LGlobal v) -> do
        update_ref ref (\ri -> Just ri { expression = Left $ EGlobal ref v })
        return (EGlobal ref v)

    Nothing -> do
        throw_UnboundVariable x

translate_expression (S.EQualified m x) _ = do
  ref <- create_ref
  id <- lookup_qualified_var (m, x)
  update_ref ref (\ri -> Just ri { expression = Left $ EGlobal ref id })
  return $ EGlobal ref id

translate_expression (S.EFun p e) label = do
  ref <- create_ref
  (p', lbl) <- translate_pattern p label
  e' <- translate_expression e $ label { L.variables = lbl }
  update_ref ref (\ri -> Just ri { expression = Left $ EFun ref p' e' })
  return (EFun ref p' e')

translate_expression (S.ELet r p e f) label = do
  -- At his point, p may be an applicative pattern,
  -- The arguments should be passed to the expression e.
  (p', lbl) <- translate_pattern p label

  e' <- case r of
        Recursive -> do
            translate_expression e $ label { L.variables = lbl }
        Nonrecursive -> do
            translate_expression e $ label
  f' <- translate_expression f $ label { L.variables = lbl }
  return (ELet r p' e' f')

translate_expression (S.EDatacon datacon e) label = do
  ref <- create_ref
  case Map.lookup datacon $ L.datacons label of
    Just id -> do
        case e of
          Just e -> do
              e' <- translate_expression e label
              update_ref ref (\ri -> Just ri { expression = Left $ EDatacon ref id $ Just e' })
              return (EDatacon ref id $ Just e')

          Nothing -> do
              update_ref ref (\ri -> Just ri { expression = Left $ EDatacon ref id Nothing })
              return (EDatacon ref id Nothing)

    Nothing -> do
        throw_UnboundDatacon datacon

translate_expression (S.EMatch e blist) label = do
  e' <- translate_expression e label
  blist' <- List.foldr (\(p, f) rec -> do
                          r <- rec
                          (p', lbl) <- translate_pattern p label
                          f' <- translate_expression f $ label { L.variables = lbl }
                          return ((p', f'):r)) (return []) blist
  return (EMatch e' blist')

-- Convert the application of a data constructor to a data constrcutor with an argument.
translate_expression (S.EApp (S.ELocated (S.EDatacon dcon Nothing) _) e) label = do
  ref <- create_ref
  e' <- translate_expression e label
  case Map.lookup dcon $ L.datacons label of
    Just id -> do
        update_ref ref (\ri -> Just ri { expression = Left $ EDatacon ref id $ Just e' })
        return (EDatacon ref id $ Just e')
    Nothing -> do
        throw_UnboundDatacon dcon

translate_expression (S.EApp e f) label = do
  e' <- translate_expression e label
  f' <- translate_expression f label
  return (EApp e' f')

translate_expression (S.ETuple elist) label = do
  ref <- create_ref
  elist' <- List.foldr (\e rec -> do
                          r <- rec
                          e' <- translate_expression e label
                          return (e':r)) (return []) elist
  update_ref ref (\ri -> Just ri { expression = Left $ ETuple ref elist' })
  return (ETuple ref elist')

translate_expression (S.EIf e f g) label = do
  e' <- translate_expression e label
  f' <- translate_expression f label
  g' <- translate_expression g label
  return (EIf e' f' g')

translate_expression (S.EBox t) label = do
  ex <- get_location
  ref <- create_ref
  t' <- translate_bound_type t label
  -- Check that the type of the box is a quantum data type
  if not (is_qdata t') then do
    prt <- pprint_type_noref t'
    throwQ (BadBoxType prt) ex

  else do
    -- The translation of the type of the box in the core syntax produces
    -- some constraints that needs to be conveyed to the type inference
    -- Using a scheme is a way of doing it
    update_ref ref (\ri -> Just ri { expression = Left $ EBox ref t' })
    return (EBox ref t')

translate_expression S.EUnbox _ = do
  ref <- create_ref
  update_ref ref (\ri -> Just ri { expression = Left $ EUnbox ref })
  return (EUnbox ref)

translate_expression S.ERev _ = do
  ref <- create_ref
  update_ref ref (\ri -> Just ri { expression = Left $ ERev ref })
  return (ERev ref)

translate_expression (S.ELocated e ex) label = do
  set_location ex
  translate_expression e label

translate_expression (S.EConstraint e t) label = do
  e' <- translate_expression e label
  return $ EConstraint e' (t, L.types label)

translate_expression e _ = do
  ref <- get_location
  throwQ (ParsingError (pprint e)) ref


