-- | This module processes the surface syntax and translates it into the internal syntax. This includes: processing of type definitions, with inference of
-- the type properties (subtyping, qdata type) ; translation of the body (with scope analysis, generation of the export list, linking with the interface) ; some
-- functions to convert the syntax to raw proto-quipper code.
--
-- The subtyping constraints {user a <: user a'} can't be interpreted as just {a <: a'}. Indeed, the order of the
-- constraints may be reversed, as is the case with the type:
--
-- @
-- type foo a b =
--   Bar of a -> b
-- @
-- 
-- Intuitively, a constraint {foo a b <: foo a' b'} is to be reduced as {a' <: a, b <: b'}, which would
-- correspond to the subtyping reltation rule:
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
-- given the type either:
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
-- * The number of possible constraints of this kind is limited: at most 2n (where n is the number of type arguments) can exist.
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
-- which is the expected subtyping relation rule. This algorithm has yet to be proved.
module Typing.TransSyntax (
  define_user_subtyping,
  define_user_properties,
  translate_type,
  translate_bound_type,
  translate_unbound_type,
  translate_expression,
  translate_pattern,
  export_pattern_variables,
  unsugar,
  import_builtins,
  import_typedefs,
  update_module_types) where

import Utils
import Classes
import Builtins

import Typing.CoreSyntax
import Typing.CorePrinter
import Typing.Subtyping

import Parsing.Localizing
import Parsing.Syntax (RecFlag (..))
import qualified Parsing.Syntax as S
import Parsing.Printer

import Interpret.Values
import Interpret.Circuits as C

import Monad.QuipperError
import Monad.QpState hiding (is_qdata_lintype, is_qdata_type)
import qualified Monad.QpState as Q (is_qdata_lintype, is_qdata_type)
import Monad.Modules

import Control.Exception

import Data.Map as Map
import qualified Data.List as List
import qualified Data.IntMap as IMap



-- | Imports the type definitions in the current state.
-- The data constructors are labelled during this operation, their associated type translated, and themselves included in the field datacons of the state.
import_typedefs :: [S.Typedef] -> QpState (Map String Int)
import_typedefs typedefs = do
  -- Import the names of the types in the current labelling map
  -- This operation permits the writing of inductive types
  List.foldl (\rec (S.Typedef typename args _) -> do
                rec
                spec <- return $ Spec { args = List.length args,
                                        bound = True,                -- Default value is True
                                        qdatatype = True,            -- qdata type by default
                                        unfolded = ([], []),
                                        subtype = ([], [], emptyset) }

                -- Register the type in the current context
                register_type typename spec

                -- Add an entry to the current module
                cm <- get_module
                ctx <- get_context
                set_context $ ctx { cmodule = cm { typespecs = Map.insert typename spec $ typespecs cm } }

                return ()) (return ()) typedefs

  -- Transcribe the rest of the type definitions
  -- Type definitions include : the name of the type, generic variables, the list of constructors
  List.foldl (\rec (S.Typedef typename args dlist) -> do
                lbl <- rec

                -- Bind the arguments of the type
                -- For each string argument a, a type !n a is created and bound in the map mapargs
                (args', mapargs) <- List.foldr (\a rec -> do
                                                  (args, m) <- rec
                                                  ta <- new_type
                                                  return (ta:args, Map.insert a ta m)) (return ([], Map.empty)) args

                -- Define the type of the data constructors
                (dtypes', m) <- List.foldr (\(dcon, dtype) rec -> do
                                             (dt, lbl) <- rec
                                             (dtype, argtyp, cset) <- case dtype of
                                                                 -- If the constructor takes no argument
                                                                 Nothing -> do
                                                                     return (TBang one (TUser typename args'), TBang one TUnit, emptyset)

                                                                 -- If the constructor takes an argument
                                                                 Just dt -> do
                                                                     (dt'@(TBang n _), cset) <- translate_bound_type dt mapargs
                                                                     return (TBang one (TArrow dt' (TBang n $ TUser typename args')), dt', cset)

                                             -- Generalize the type of the constructor over the free variables and flags
                                             -- Those variables must also respect the constraints from the construction of the type
                                             (fv, ff) <- return (free_typ_var dtype, free_flag dtype)
                                             dtype <- return $ TForall ff fv cset dtype

                                             -- Register the datacon
                                             id <- register_datacon dcon dtype
                                             return $ (argtyp:dt, Map.insert dcon id lbl)) (return ([], lbl)) dlist

                -- Update the specification of the type
                spec <- type_spec typename
                ctx <- get_context
                set_context $ ctx { types = Map.insert typename (spec { unfolded = (args', List.map (\t -> (0, False, t)) dtypes') }) $ types ctx }
                return m) (return Map.empty) typedefs





-- | Unfold the definitions of the types in the subtyping constraints
-- products of the reduction of user a <: user a'
-- Takes the name of the type as input, and returns the resulting set.
-- No modification is made to the specification of the type.
unfold_once :: String -> QpState ConstraintSet
unfold_once name = do
  spec <- type_spec name
  
  -- Unfolded constraints
  (a, a', current) <- return $ subtype spec
  
  -- unfold the user type constraints
  cuser <- unfold_user_constraints_in_set current

  -- Break the composite constraints, although without touching
  -- the user type constraints, thus the false flag in the call to break_composite
  cuser <- break_composite False cuser

  -- Add them one by one to the non user constraints, checking
  -- for duplicates
  lcuser <- return $ List.nub (fst cuser)
  fcuser <- return $ List.nub (snd cuser)
  return (lcuser, fcuser)


-- | Unfold the definitions of the types in the subtyping constraints untils the
-- resulting constraint set becomes stable. The input is a list of co-inductive
-- types. It doesn't output anything, but updates the constraint set in the specification
-- of the input types
unfold_all :: [String] -> QpState ()
unfold_all [] = return ()
unfold_all names = do
  -- Get all the specifications
  specs <- List.foldr (\n rec -> do 
                         r <- rec
                         s <- type_spec n
                         return (s:r)) (return []) names

  -- Unfold all
  unfolded <- List.foldr (\n rec -> do
                             r <- rec
                             uf <- unfold_once n
                             return (uf:r)) (return []) names

  -- Compare the set after unfolding to before unfolding
  -- If any has been changed, go for another round, else
  -- end
  ctx <- get_context
  (finish, ctx) <- List.foldl (\rec (n, spec, after) -> do
                                 (b, ctx) <- rec
                                 (a, a', subt) <- return $ subtype spec
                                 before <- return $ (List.filter (not . is_user) (fst subt), snd subt)
                                 (cuser, cnuser) <- return $ (let (lc, lc') = List.partition is_user (fst after) in
                                                              (lc, (lc', snd after)))
                          
                                 -- Check the stability of the non user constraints of before and after the unfolding
                                 if before `equals_set` cnuser then do
                                   -- Terminate the recursion, and retain in the subtyping of n only the non user constraints
                                   newlog 0 ("[" ++ List.foldl (\rec c -> " " ++ pprint c ++ rec) "" (fst before) ++ 
                                                    List.foldl (\rec c -> " " ++ pprint c ++ rec) "" (snd before) ++ " ] => " ++
                                             pprint (TUser n a) ++ " <: " ++ pprint (TUser n a'))

                                   return (b, ctx { types = Map.insert n (spec { subtype = (a, a', before) }) $ types ctx })
                                 else do
                                   -- Continue the recursion, but update the subtyping of n
                                   return (n:b, ctx { types = Map.insert n (spec { subtype = (a, a', after) }) $ types ctx })) (return ([], ctx)) (List.zip3 names specs unfolded) 

  -- Continue or not with the recursion
  set_context ctx
  unfold_all finish


-- | Infers the subtyping relation rules of all the user defined types.
-- It uses the algorithm described above.
define_user_subtyping :: [S.Typedef] -> QpState () 
define_user_subtyping typedefs = do
  newlog 0 ">> User subtyping relations"
  -- Get the type names
  names <- return $ List.map (\(S.Typedef n _ _) -> n) typedefs

  -- Initialize the constraint set of each user type
  List.foldl (\rec n -> do
                rec
                spec <- type_spec n
                -- One version of the unfolded type
                (a, ufold) <- return $ unfolded spec
                -- Another version of the unfolded type, where a has been replaced by fresh types a'
                (a', ufold') <- List.foldr (\(TBang n (TVar x)) rec -> do
                                              (a', ufold') <- rec
                                              b@(TBang m (TVar y)) <- new_type
                                              ufold' <- return $ List.map (\(dcon, bound, typ) -> (dcon, bound, subs_typ_var x (TVar y) typ)) ufold'
                                              ufold' <- return $ List.map (\(dcon, bound, typ) -> (dcon, bound, subs_flag n m typ)) ufold'
                                              return (b:a', ufold')) (return ([], ufold)) a

                -- Generate the constraints ufold <: ufold'
                constraints <- List.foldl (\rec ((_, _, t), (_, _, u)) -> do
                                             r <- rec
                                             cset <- break_composite False ([t <: u], [])    -- We don't want the user type constraints to be replaced yet
                                             return $ cset <> r) (return emptyset) (List.zip ufold ufold')

                ctx <- get_context
                set_context $ ctx { types = Map.insert n (spec { subtype = (a, a', constraints) }) $ types ctx }) (return ()) names

  -- Unfold until the constraint set is stable
  unfold_all names
  newlog 0 "<<\n"



-- | Function specifically used by define_user_properties to check qdata types. The list of names correspond to the list
-- of unsolved types. When a user type of this list is encountered, it is added to the list of dependencies, and the data check
-- is delayed till later.
is_qdata_lintype :: LinType -> [String] -> QpState (Bool, [String])
is_qdata_lintype TQubit _ =
  return (True, [])

is_qdata_lintype TUnit _ =
  return (True, [])

is_qdata_lintype (TTensor tlist) names =
  List.foldl (\rec t -> do
                (b, deps) <- rec
                if b then do
                  (b', deps') <- is_qdata_type t names
                  return (b', List.union deps deps')
                else
                  return (False, [])) (return (True, [])) tlist

-- We stil check whether the arguments are of qdata type
is_qdata_lintype (TUser typename args) names = do
  -- Check the type of the arguments
  (b, deps) <- List.foldl (\rec t -> do
                             (b, deps) <- rec
                             if b then do
                               (b', deps') <- is_qdata_type t names
                               return (b', List.union deps deps')
                             else
                               return (False, [])) (return (True, [])) args
  -- If the arguments are ok, check the type (iff it is not in the list
  if b && (not $ List.elem typename names) then do
    spec <- type_spec typename
    return (qdatatype spec, deps)
  else
    return (b, typename:deps)

is_qdata_lintype _ _ = 
  return (False, [])



-- | Function specifically used by define_user_properties to check qdata types. The list of names correspond to the list
-- of unsolved types. When a user type of this list is encountered, it is added to the list of dependencies, and the data check
-- is delayed till later.
is_qdata_type :: Type -> [String] -> QpState (Bool, [String])
is_qdata_type (TBang _ a) names =
  is_qdata_lintype a names 



-- | Inputs a list of types that verify a property, and a graph of consequences. Then the function propagates the
-- property to the dependencies in the graph, modifying the graph in so doing.
propagate_prop :: [String] -> Map String [String] -> ([String], Bool, Map String [String])
propagate_prop [] graph =
  ([], False, graph)

propagate_prop (n:rest) graph =
  case Map.lookup n graph of
    Just deps -> 
        let (r', c, g') = propagate_prop (List.union rest deps) (Map.delete n graph) in
        (n:r', True, g')

    Nothing ->
        let (r', c, g') = propagate_prop rest graph in
        if c then
          propagate_prop (n:r') g'
        else
          (n:r', False, g')


-- | Defines the user property: qdatatype. This property can only be defined for all the types taken at the same time.
-- This function first builds a graph of dependencies indicating which type uses which type in the type of the data
-- constructors. Some types are clearly marked as being non quantum data types. In the graph of dependencies, all the types
-- using these non-quantum types cannot in turn be qdata types ; and so on. After all the non qdata types have been eliminated,
-- all that remain are qdata types.
define_user_properties :: [S.Typedef] -> QpState ()
define_user_properties typedefs = do
  -- A specific function is needed to check quantum data types
    newlog 0 ">> User type properties"
    -- Get the names
    names <- return $ List.map (\(S.Typedef n _ _) -> n) typedefs

    -- Creates the map of dependencies of qdata type properties
    -- The edges are oriented so that if one of the types doesn't have a property, then neither should the dependencies.
    (mbound, mdata, mgraph) <- List.foldl (\rec n -> do
                                 (mbound, mdata, mgraph) <- rec
                                 spec <- type_spec n
                                 -- Replace the arguments by qubit in the unfolded definition
                                 argtyps <- return $ List.map (\(_, _, argtyp) ->
                                                                 List.foldl (\a (TBang _ (TVar x)) ->
                                                                               subs_typ_var x TQubit a) argtyp $ fst $ unfolded spec) (snd $ unfolded spec)
                                 -- Check each of the types for qdata types
                                 (b, deps) <- List.foldl (\rec a -> do
                                                            (b, deps) <- rec
                                                            if b then do
                                                              (b', deps') <- is_qdata_type a names
                                                              return (b', List.union deps' deps)
                                                            else
                                                              return (False, [])) (return (True, [])) argtyps

                                 -- Increase the map
                                 if b then do
                                   return (mbound, mdata, List.foldl (\m d ->
                                                                        case Map.lookup d m of
                                                                          Just l -> Map.insert d (n:l) m
                                                                          Nothing -> Map.insert d [n] m) mgraph deps)
                                 else do
                                   return (mbound, n:mdata, mgraph)) (return ([], [], Map.empty)) names

    -- Solve the map, and set the qdata properties
    (mdata', _, _) <- return $ propagate_prop mdata mgraph
    List.foldl (\rec n -> do
                  rec
                  if List.elem n mdata' then do
                    -- Not a qdata type
                    newlog 0 $ "-- " ++ n ++ " is not a quantum data type"
                    ctx <- get_context
                    spec <- type_spec n
                    set_context $ ctx { types = Map.insert n (spec { qdatatype = False }) $ types ctx }
                  else do
                    -- QData type
                    newlog 0 $ "-- " ++ n ++ " may be a quantum data type"
                    -- Since the default value is True, no need to set it here)
                    return ()) (return ()) names
                

    newlog 0 "<<\n"


-- | Transfers the type definitions from the state monad to the current module.
-- This function assumes that the current module already have entries corresponding to its types, and
-- just updates them.
update_module_types :: QpState ()
update_module_types = do
  cmod <- get_module
  cmod' <- Map.foldWithKey (\typename _ rec -> do
                              cm <- rec
                              spec <- type_spec typename
                              return $ cm { typespecs = Map.insert typename spec (typespecs cm) }) (return cmod) (typespecs cmod)
  ctx <- get_context
  set_context $ ctx { cmodule = cmod' }


-- | Imports the builtin values, defined in the "Builtins" module.
import_builtins :: QpState ()
import_builtins = do
  mb <- Map.foldWithKey (\b (t, v) rec -> do
                      m <- rec
                      (t', _) <- translate_bound_type t Map.empty
                      return $ Map.insert b (t', v) m) (return Map.empty) (Map.union builtin_gates builtin_operations)
  ctx <- get_context
  set_context $ ctx { builtins = mb }


-- | Translate a type, given a labelling.
-- The output includes a set of structural constraints: eg !p (!n a * !m b) imposes p <= n and p <= m.
translate_type :: S.Type
               -> [Type]                  -- ^ List of type arguments. Only when the type is algebraic may this list not be empty.
               -> (Map String Type, Bool) -- ^ A map of bound type variables. The boolean flag indicates how to deal with unbound variables:
                                          -- they can either:
                                          --
                                          -- * generate a typing error (the definition of algebraic types doesn't allow for unbound variables).
                                          --
                                          -- * be bound in the map (all other cases).
               -> QpState (Type, ConstraintSet, Map String Type)
translate_type S.TUnit [] m = do
  return (TBang one TUnit, emptyset, fst m)

translate_type S.TBool [] m = do
  return (TBang one TBool, emptyset, fst m)

translate_type S.TInt [] m = do
  return (TBang one TInt, emptyset, fst m)

translate_type S.TQubit [] m = do
  return (TBang zero TQubit, emptyset, fst m)

translate_type (S.TVar x) arg (label, bound) = do
  case Map.lookup x label of
    -- All the registered variables are bound variables from a type definition or a constraint
    Just typ ->
        if arg == [] then
          return (typ, emptyset, label)
        else do
          ex <- get_location
          f <- get_file
          throw $ LocatedError (WrongTypeArguments (pprint typ) 0 (List.length arg)) (f, ex)

    -- If the variable is not found, it can be either a user type,
    -- or a free variable (depending on the boolean arg)
    Nothing -> do
        ctx <- get_context
        -- The variable is a algebraic type
        if Map.member x $ types ctx then do

          -- Expected number of args
          spec <- type_spec x
          nexp <- return $ args spec
          -- Actual number of args
          nact <- return $ List.length arg

          if nexp == nact then do
            n <- fresh_flag
            return (TBang n (TUser x arg), emptyset, label)
          else do
            ex <- get_location
            f <- get_file
            throw $ LocatedError (WrongTypeArguments x nexp nact) (f, ex)
        
        else if bound then do
          -- If the type variables are supposed to be bound, this one isn't
          ex <- get_location
          f <- get_file
          throw $ LocatedError (UnboundVariable x) (f, ex)

        else do
          -- Last case, if the type authorize free variables, register this one with a new type
          t <- new_type
          return (t, emptyset, Map.insert x t label)


translate_type (S.TQualified m x) arg lbl = do
  spec <- lookup_qualified_type (m, x)
  -- Expected number of args
  nexp <- return $ args spec
  -- Actual number of args
  nact <- return $ List.length arg

  if nexp == nact then do
    n <- fresh_flag
    return (TBang n (TUser x arg), emptyset, fst lbl)
  else do
    ex <- get_location
    f <- get_file
    throw $ LocatedError (WrongTypeArguments x nexp nact) (f, ex)

translate_type (S.TArrow t u) [] (label, bound) = do
  (t', csett, lblt) <- translate_type t [] (label, bound)
  (u', csetu, lblu) <- translate_type u [] (lblt, bound)
  n <- fresh_flag
  return (TBang n (TArrow t' u'), csett <> csetu, lblu)

translate_type (S.TTensor tlist) [] (label, bound) = do
  n <- fresh_flag
  (tlist', cset', lbl) <- List.foldr (\t rec -> do
                                        (r, cs, lbl) <- rec
                                        (t'@(TBang m _), cs', lbl') <- translate_type t [] (lbl, bound)
                                        return ((t':r), [(Le n  m no_info)] <> cs' <> cs, lbl')) (return ([], emptyset, label)) tlist
  return (TBang n (TTensor tlist'), cset', lbl)

translate_type (S.TBang t) [] label = do
  (TBang _ t, cset, lbl) <- translate_type t [] label
  return (TBang 1 t, cset, lbl)

translate_type (S.TCirc t u) [] (label, bound) = do
  (t', csett, lblt) <- translate_type t [] (label, bound)
  (u', csetu, lblu) <- translate_type u [] (lblt, bound)
  return (TBang one (TCirc t' u'), csett <> csetu, lblu)

-- Case of type application : the argument is pushed onto the arg list
translate_type (S.TApp t u) args (label, bound) = do
  (u', cset, lblt) <- translate_type u [] (label, bound)
  (t', cset', lblu) <- translate_type t (u':args) (lblt, bound)
  return (t', cset <> cset', lblu)

translate_type (S.TLocated t ex) args label = do
  set_location ex
  translate_type t args label

-- Remaining cases : of types applied to an argument when they are not generic
translate_type t args label = do
  ex <- get_location
  f <- get_file
  throw $ LocatedError (WrongTypeArguments (pprint t) 0 (List.length args)) (f, ex)



-- | The function 'Typing.TransSyntax.translate_type' applied to a bound type.
-- The arguments are supposed to be null initially.
translate_bound_type :: S.Type -> Map String Type -> QpState (Type, ConstraintSet)
translate_bound_type t m = do
  (t', cset, _) <- translate_type t [] (m, True)
  return (t', cset)



-- | The function 'Typing.TransSyntax.translate_type' applied to unbound types.
-- The binding map is initially empty, and is dropped after the translation of the type
-- No argument is passed to the top type.
translate_unbound_type :: S.Type -> QpState (Type, ConstraintSet)
translate_unbound_type t = do
  (t', cset, _) <- translate_type t [] (Map.empty, False)
  return (t', cset)



-- | Translates a pattern, given a labelling map.
-- The map is updated as variables are bound in the pattern.
translate_pattern :: S.Pattern -> Map String Int -> QpState (Pattern, Map String Int)
translate_pattern S.PUnit label = do
  return (PUnit, label)

translate_pattern S.PJoker label = do
  return (PJoker, label)

translate_pattern (S.PVar x) label = do
  ex <- get_location
  id <- register_var x ex
  return (PVar id, Map.insert x id label)

translate_pattern (S.PTuple plist) label = do
  (plist', lbl) <- List.foldr (\p rec -> do
                                  (r, lbl) <- rec
                                  (p', lbl') <- translate_pattern p lbl
                                  return ((p':r), lbl')) (return ([], label)) plist
  return (PTuple plist', lbl)

translate_pattern (S.PDatacon datacon p) label = do
  case Map.lookup datacon label of
    Just id -> do
        case p of
          Just p -> do
              (p', lbl) <- translate_pattern p label
              return (PDatacon id (Just p'), lbl)

          Nothing ->
              return (PDatacon id Nothing, label)

    Nothing -> do
        ex <- get_location
        f <- get_file
        throw $ LocatedError (UnboundDatacon datacon) (f, ex)

translate_pattern (S.PLocated p ex) label = do
  set_location ex
  (p', lbl) <- translate_pattern p label
  return (PLocated p' ex, lbl)


translate_pattern (S.PConstraint p t) label = do
  (p', lbl) <- translate_pattern p label
  return (PConstraint p' t, lbl)



-- | Translates an expression, given a labelling map
translate_expression :: S.Expr -> Map String Variable -> QpState Expr
translate_expression S.EUnit _ = do
  return EUnit

translate_expression (S.EBool b) _ = do
  return (EBool b)

translate_expression (S.EInt n) _ = do
  return (EInt n)

translate_expression (S.EVar x) label = do
  case Map.lookup x label of
    Just id -> do
        ctx <- get_context
        if List.elem id $ IMap.keys $ globals ctx then
          return $ EGlobal id
        else
          return $ EVar id

    Nothing -> do
        ex <- get_location
        f <- get_file
        throw $ LocatedError (UnboundVariable x) (f, ex)

translate_expression (S.EQualified m x) _ = do
  id <- lookup_qualified_var (m, x)
  return $ EGlobal id

translate_expression (S.EFun p e) label = do
  (p', lbl) <- translate_pattern p label
  e' <- translate_expression e lbl
  return (EFun p' e')

translate_expression (S.ELet r p e f) label = do
  (p', lbl) <- translate_pattern p label
  case r of
    Recursive -> do
        e' <- translate_expression e lbl
        f' <- translate_expression f lbl
        return (ELet r p' e' f')

    Nonrecursive -> do
        e' <- translate_expression e label
        f' <- translate_expression f lbl
        return (ELet r p' e' f')

translate_expression (S.EDatacon datacon e) label = do
  case Map.lookup datacon label of
    Just id -> do
        case e of
          Just e -> do
              e' <- translate_expression e label
              return (EDatacon id $ Just e')

          Nothing ->
              return (EDatacon id Nothing)

    Nothing -> do
        ex <- get_location
        f <- get_file
        throw $ LocatedError (UnboundDatacon datacon) (f, ex)

translate_expression (S.EMatch e blist) label = do
  e' <- translate_expression e label
  blist' <- List.foldr (\(p, f) rec -> do
                          r <- rec
                          (p', lbl) <- translate_pattern p label
                          f' <- translate_expression f lbl
                          return ((p', f'):r)) (return []) blist
  return (EMatch e' blist')

translate_expression (S.EApp e f) label = do
  e' <- translate_expression e label
  f' <- translate_expression f label
  return (EApp e' f')

translate_expression (S.ETuple elist) label = do
  elist' <- List.foldr (\e rec -> do
                          r <- rec
                          e' <- translate_expression e label
                          return (e':r)) (return []) elist
  return (ETuple elist')

translate_expression (S.EIf e f g) label = do
  e' <- translate_expression e label
  f' <- translate_expression f label
  g' <- translate_expression g label
  return (EIf e' f' g')

translate_expression (S.EBox t) _ = do
  ex <- get_location
  (t', cset) <- translate_bound_type t Map.empty
  -- Check that the type of the box is a quantum data type
  qdata <- Q.is_qdata_type t'
  if not qdata then do
    prt <- pprint_type_noref t'
    f <- get_file
    throwQ $ LocatedError (BoxTypeError prt) (f, ex)

  else
    -- The translation of the type of the box in the core syntax produces
    -- some constraints that needs to be conveyed to the type inference
    -- Using a scheme is a way of doing it
    return (EBox (TForall [] [] cset t'))

translate_expression S.EUnbox _ = do
  return EUnbox

translate_expression S.ERev _ = do
  return ERev

translate_expression (S.ELocated e ex) label = do
  set_location ex
  e' <- translate_expression e label
  return $ ELocated e' ex

translate_expression (S.EBuiltin s) _ = do
  -- Check the existence of the builtin value before translating it
  ctx <- get_context
  if Map.member s $ builtins ctx then
    -- Ok, the builtin s exists
    return $ EBuiltin s
  else do
    -- Wrong, no builtin of name s has been defined
    ex <- get_location
    f <- get_file
    throwQ $ LocatedError (UndefinedBuiltin s) (f, ex)

translate_expression (S.EConstraint e t) label = do
  e' <- translate_expression e label
  return $ EConstraint e' t



-- | Exports the variables of a pattern. If an interface file is provided, it first checks
-- whether the variables are part of the accessible variables :
--
--      *  if yes, it exports the variables, and modifies the pattern to add a constraint on the type fo this variable
--
--      *  if not, does nothing
--
export_pattern_variables :: S.Program -> Pattern -> QpState Pattern
export_pattern_variables _ PUnit =
  return PUnit

export_pattern_variables prog (PLocated p _) =
  export_pattern_variables prog p

export_pattern_variables prog (PVar x) = do
  case S.interface prog of
    Just inter -> do
        -- If an interface file is present, check the presence of the variable x
        n <- variable_name x
        case List.lookup n inter of
          Just typ -> do
              export_var x
              return $ PConstraint (PVar x) typ

          Nothing -> do
              return $ PVar x

    Nothing -> do
        export_var x
        return $ PVar x

export_pattern_variables prog (PDatacon dcon Nothing) =
  return $ PDatacon dcon Nothing

export_pattern_variables prog (PDatacon dcon (Just p)) = do
  p' <- export_pattern_variables prog p
  return $ PDatacon dcon $ Just p'

export_pattern_variables prog (PTuple plist) = do
  plist' <- List.foldr (\p rec -> do
                          r <- rec
                          p' <- export_pattern_variables prog p
                          return (p':r)) (return []) plist
  return $ PTuple plist


-- | All the following functions serve to translate the program implementatioin and
-- types into the proto core, meaning without all the syntactic sugars


-- | Transform a type A * B * C * D into A * (B * (C * D))
unfold_tensors_in_lintype :: LinType -> QpState LinType
unfold_tensors_in_lintype (TVar a) =
  return $ TVar a

unfold_tensors_in_lintype (TArrow a b) = do
  a' <- unfold_tensors a
  b' <- unfold_tensors b
  return $ TArrow a' b'

unfold_tensors_in_lintype TUnit =
  return TUnit

unfold_tensors_in_lintype (TTensor tlist) = do
  case tlist of
    [a, b] -> do
        a' <- unfold_tensors a
        b' <- unfold_tensors b
        return $ TTensor [a', b']

    (a:rest) -> do
        a' <- unfold_tensors a
        rest' <- unfold_tensors_in_lintype $ TTensor rest
        n <- fresh_flag
        return $ TTensor [a', TBang n rest']

unfold_tensors_in_lintype TBool =
  return TBool

unfold_tensors_in_lintype TInt =
  return TInt

unfold_tensors_in_lintype TQubit =
  return TQubit

unfold_tensors_in_lintype (TCirc a b) = do
  a' <- unfold_tensors a
  b' <- unfold_tensors b
  return $ TCirc a' b'

unfold_tensors_in_lintype (TUser typename arg) = do
  arg' <- List.foldr (\a rec -> do
                        r <- rec
                        a' <- unfold_tensors a
                        return $ a':r) (return []) arg
  return $ TUser typename arg'


-- | Same for types
unfold_tensors :: Type -> QpState Type
unfold_tensors (TBang n a) = do
  a' <- unfold_tensors_in_lintype a
  return $ TBang n a'



-- | Transform a pattern <a, b, c, d> into <a, <b, <c, d>>>
unfold_tuples :: Pattern -> Pattern
unfold_tuples (PLocated p ex) =
  PLocated (unfold_tuples p) ex

unfold_tuples PUnit =
  PUnit

unfold_tuples (PVar x) =
  (PVar x)

unfold_tuples (PDatacon dcon Nothing) =
  (PDatacon dcon Nothing)

unfold_tuples (PDatacon dcon (Just p)) =
  let p' = unfold_tuples p in
  PDatacon dcon $ Just p'

unfold_tuples (PTuple plist) =
  case plist of
    [p, q] ->
        let p' = unfold_tuples p
            q' = unfold_tuples q in
        PTuple [p', q']

    (p:rest) ->
        let p' = unfold_tuples p
            rest' = unfold_tuples $ PTuple rest in
        PTuple [p', rest']


-- | Removes all the syntactic sugars of an expression.
-- This function operates on core expressions. As sugars are removed, new variables are
-- produced.
unsugar :: Expr -> QpState Expr

unsugar (EVar x) =
  return $ EVar x

unsugar (EGlobal x) =
  return $ EGlobal x

unsugar (EFun p e) = do
   -- Check whether the expression is already unsugared or not
  case p of
    -- The pattern is only one variable : do nothing
    PVar _ -> do
      e' <- unsugar e
      return $ EFun p e'

    -- If the pattern is more complicated, replace it by a variable
    _ -> do
      x <- dummy_var
      e' <- unsugar $ ELet Nonrecursive p (EVar x) e
      return $ EFun (PVar x) e'

unsugar (EApp e f) = do
  e' <- unsugar e
  f' <- unsugar f
  return $ EApp e' f'

unsugar EUnit = do
  return EUnit

-- Tuples are a syntactic sugar for chained pairs :
-- the tuple <a, b, c, d> is the pattern <a, <b, <c, d>>>
unsugar (ETuple elist) = do
  case elist of
    -- This is the minimum size tuple, and is left as is
    [e,f] -> do
        e' <- unsugar e
        f' <- unsugar f
        return $ ETuple [e', f']

    -- With more elements : unsugar the rest, and 'append' the head on the left
    (e:rest) -> do
        e' <- unsugar e
        rest' <- unsugar $ ETuple rest
        return $ ETuple [e', rest']

    -- The other cases of empty and sinleton tuples shouldn't appear

unsugar (ELet r p e f) = do
  p' <- return $ unfold_tuples p
  e' <- unsugar e
  case p' of
    -- If the pattern is unit : do nothing
    PUnit -> do
        f' <- unsugar f
        return $ ELet r p' e' f'

    -- If the pattern is one variable, do nothing
    -- The let binding can't be removed because of let-polymorphism
    PVar _ -> do
        f' <- unsugar f
        return $ ELet r p' e' f'

    -- If the pattern is a pair of variables, this is the case of tensor elimination
    PTuple [PVar _, PVar _] -> do
        f' <- unsugar f
        return $ ELet r p' e' f'

    -- If one of the elements of the pattern is not a variable, unsugar
    PTuple [PVar x, q] -> do
        y <- dummy_var
        f' <- unsugar $ ELet r q (EVar y) f
        return $ ELet r (PTuple [PVar x, PVar y]) e' f'

    PTuple [p, PVar x] -> do
        y <- dummy_var
        f' <- unsugar $ ELet r p (EVar y) f
        return $ ELet r (PTuple [PVar y, PVar x]) e' f'

    PTuple [p, q] -> do
        x <- dummy_var
        y <- dummy_var
        f' <- unsugar $ ELet r p (EVar x) (ELet r q (EVar y) f)
        return $ ELet Nonrecursive (PTuple [PVar x, PVar y]) e' f'

    -- If the pattern is a datacon, unsugar by adding a pattern matching
    PDatacon dcon Nothing -> do
        f' <- unsugar f
        return $ EMatch e' [(PDatacon dcon Nothing, f')]

    PDatacon dcon (Just p) -> do
        case p of
          PVar x -> do
              f' <- unsugar f
              return $ EMatch e' [(PDatacon dcon $ Just p, f')]

          _ -> do
              x <- dummy_var
              f' <- unsugar (ELet Nonrecursive p (EVar x) f)
              return $ EMatch e' [(PDatacon dcon $ Just (PVar x), f')]

    _ -> return $ ELet r p e f

unsugar (EBool b) = do
  return $ EBool b

unsugar (EInt n) = do
  return $ EInt n

unsugar (EIf e f g) = do
  e' <- unsugar e
  f' <- unsugar f
  g' <- unsugar g
  return $ EIf e' f' g'

unsugar (EDatacon dcon Nothing) = do
  return $ EDatacon dcon Nothing

unsugar (EDatacon dcon (Just e)) = do
  e' <- unsugar e
  return $ EDatacon dcon $ Just e'

unsugar (EMatch e blist) = do
  e' <- unsugar e
  blist' <- List.foldr (\(p, f) rec -> do
                          r <- rec
                          case p of
                            PDatacon dcon Nothing -> do
                                f' <- unsugar f
                                return $ (PDatacon dcon Nothing, f'):r

                            PDatacon dcon (Just p) -> do
                                x <- dummy_var
                                f' <- unsugar $ ELet Nonrecursive p (EVar x) f
                                return $ (PDatacon dcon $ Just (PVar x), f'):r) (return []) blist

                            -- The other cases are ignored for now, as syntactic equlity hasn't been developped yet
  return $ EMatch e' blist'

unsugar (EBox typ) = do
  return $ EBox typ

unsugar EUnbox = do
  return EUnbox

unsugar ERev = do
  return ERev

unsugar (ELocated e ex) = do
  e' <- unsugar e
  return $ ELocated e' ex 

