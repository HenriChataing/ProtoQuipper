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
module Typing.TransSyntax (
  define_user_subtyping,
  define_user_properties,
  translate_type,
  translate_bound_type,
  translate_unbound_type,
  translate_expression,
  translate_pattern,
  with_interface,
  desugar,
  import_builtins,
  import_typedefs,
  LabellingContext (..),
  empty_label) where

import Utils
import Classes
import Builtins

import Typing.CoreSyntax
import Typing.CorePrinter
import Typing.Subtyping

import Parsing.Location
import Parsing.Syntax (RecFlag (..))
import qualified Parsing.Syntax as S
import Parsing.Printer

import Interpret.Values
import Interpret.Circuits as C

import Monad.QuipperError
import Monad.QpState hiding (is_qdata_lintype, is_qdata_type)
import qualified Monad.QpState as Q (is_qdata_lintype, is_qdata_type)
import Monad.Modules (Module)
import qualified Monad.Modules as M

import Control.Exception

import Data.Map as Map
import qualified Data.List as List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap


-- | Labelling context: it contains the variable identifiers of all the variables, data constructors,
-- types in scope.
data LabellingContext = LblCtx {
  l_variables :: Map String LVariable,
  l_datacons :: Map String Datacon,
  l_types :: Map String Type
}



-- | Empty labelling map.
empty_label :: LabellingContext
empty_label = LblCtx {
  l_variables = Map.empty,
  l_datacons = Map.empty,
  l_types = Map.empty
}



-- | Import the built-in values, defined in the "Builtins" module.
import_builtins :: QpState ()
import_builtins = do
  mb <- Map.foldWithKey (\b (t, v) rec -> do
                      m <- rec
                      t' <- translate_bound_type t empty_label 
                      return $ Map.insert b (t', v) m) (return Map.empty) builtin_all
  ctx <- get_context
  set_context $ ctx { builtins = mb }


-- | Import the type definitions in the current state.
-- The data constructors are labelled during this operation, their associated type translated, and themselves included in the field datacons of the state.
import_typedefs :: [S.Typedef]            -- ^ A block of co-inductive type definitions.
                -> LabellingContext       -- ^ The current labelling context.
                -> QpState LabellingContext -- ^ The updated labelling context.
import_typedefs dblock label = do
  -- Import the type definitions.
  -- At first, the definition is empty, it will be elaborated later.
  -- The types of the block are added to the labelling map: this is what allows for co-inductive types
  (typs, names) <- List.foldl (\rec def@(S.Typedef typename args _) -> do
                                 (typs, names) <- rec
                                 spec <- return $ Typedef { d_args = List.length args,
                                                            d_qdatatype = True,            -- qdata type by default
                                                            d_unfolded = ([], []),
                                                            d_subtype = ([], [], emptyset) }

                                 -- Register the type in the current context
                                 id <- register_typedef typename spec
                                 -- Add the type in the map
                                 return (Map.insert typename (TBang 0 $ TUser id []) typs, id:names)) (return (l_types label, [])) dblock

  -- Transcribe the rest of the type definitions.
  -- Type definitions include: the name of the type, generic variables, the list of constructors
  datas <- List.foldl (\rec (S.Typedef typename args dlist) -> do
                         lbl <- rec
                         -- Type id needed for udpates.
                         id <- case Map.lookup typename typs of
                                 Just (TBang _ (TUser id _)) -> return id
                                 _ -> throwQ $ ProgramError "missing type id"

                         -- Bind the arguments of the type.
                         -- For each string argument a, a type !n a is created and bound in the map mapargs.
                         (args', mapargs) <- List.foldr (\a rec -> do
                                                           (args, m) <- rec
                                                           ta <- new_type
                                                           return (ta:args, Map.insert a ta m)) (return ([], typs)) args

                         -- Define the type of the data constructors
                         (dtypes', m) <- List.foldr (\(dcon, dtype) rec -> do
                                                      (dt, lbl) <- rec
                                                      (dtype, argtyp, cset) <- case dtype of
                                                                                -- If the constructor takes no argument
                                                                                Nothing -> do
                                                                                    return (TBang one (TUser id args'), TBang one TUnit, emptyset)
      
                                                                                -- If the constructor takes an argument
                                                                                Just dt -> do
                                                                                    dt'@(TBang n _) <- translate_bound_type dt $ empty_label { l_types = mapargs }
                                                                                    m <- fresh_flag
                                                                                    return (TBang one (TArrow dt' (TBang m $ TUser id args')), dt', ([], [Le m n no_info]))
 
                                                      -- Generalize the type of the constructor over the free variables and flags
                                                      -- Those variables must also respect the constraints from the construction of the type
                                                      (fv, ff) <- return (free_typ_var dtype, free_flag dtype)
                                                      dtype <- return $ TForall ff fv cset dtype

                                                      -- Register the datacon
                                                      id <- register_datacon dcon dtype
                                                      return $ (argtyp:dt, Map.insert dcon id lbl)) (return ([], lbl)) dlist

                         -- Update the specification of the type
                         Left spec <- type_spec id
                         ctx <- get_context
                         set_context $ ctx { types = IMap.insert id (Left $ spec { d_unfolded = (args', List.map (\t -> (0, t)) dtypes') }) $ types ctx }
                         return m) (return $ l_datacons label) dblock


  -- Infer the properties of the user types
  define_user_subtyping names
  define_user_properties names

  -- Return the updated labelling map for types, and the map for dataconstructors.
  return $ label { l_datacons = datas,
                   l_types = typs }



-- | Unfold the definitions of the types in the subtyping constraints
-- products of the reduction of user a <: user a'
-- Takes the name of the type as input, and returns the resulting set.
-- No modification is made to the specification of the type.
unfold_once :: Variable -> QpState ConstraintSet
unfold_once name = do
  Left spec <- type_spec name
  
  -- Unfolded constraints
  (a, a', current) <- return $ d_subtype spec
  
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
unfold_all :: [Variable] -> QpState ()
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
  (finish, ctx) <- List.foldl (\rec (n, s, after) -> do
                                 let spec = case s of
                                       Left spec -> spec
                                       _ -> throw $ ProgramError "unfold_all: bad spec"
                                 (b, ctx) <- rec
                                 (a, a', subt) <- return $ d_subtype spec
                                 before <- return $ (List.filter (not . is_user) (fst subt), snd subt)
                                 (cuser, cnuser) <- return $ (let (lc, lc') = List.partition is_user (fst after) in
                                                              (lc, (lc', snd after)))
                          
                                 -- Check the stability of the non user constraints of before and after the unfolding
                                 if before `equals_set` cnuser then do
                                   -- Terminate the recursion, and retain in the subtyping of n only the non user constraints
                                   newlog 0 ("[" ++ List.foldl (\rec c -> " " ++ pprint c ++ rec) "" (fst before) ++ 
                                                    List.foldl (\rec c -> " " ++ pprint c ++ rec) "" (snd before) ++ " ] => " ++
                                             pprint (TUser n a) ++ " <: " ++ pprint (TUser n a'))

                                   return (b, ctx { types = IMap.insert n (Left spec { d_subtype = (a, a', before) }) $ types ctx })
                                 else do
                                   -- Continue the recursion, but update the subtyping of n
                                   return (n:b, ctx { types = IMap.insert n (Left spec { d_subtype = (a, a', after) }) $ types ctx })) (return ([], ctx)) (List.zip3 names specs unfolded) 

  -- Continue or not with the recursion
  set_context ctx
  unfold_all finish


-- | Infer the subtyping relation rules of all the user defined types.
-- It uses the algorithm described above.
define_user_subtyping :: [Variable] -> QpState () 
define_user_subtyping dblock = do
  newlog 0 ">> User subtyping relations"

  -- Initialize the constraint set of each user type
  List.foldl (\rec n -> do
                rec
                s <- type_spec n
                let spec = case s of
                      Left spec -> spec
                      _ -> throw $ ProgramError "define_user_subtyping: bad spec"
                -- One version of the unfolded type
                (a, ufold) <- return $ d_unfolded spec
                -- Another version of the unfolded type, where a has been replaced by fresh types a'
                (a', ufold') <- List.foldr (\(TBang n t) rec -> do
                                              let x = case t of 
                                                     TVar x -> x
                                                     _ -> throw $ ProgramError "define_user_subtyping: non-atomic constraint"
                                              (a', ufold') <- rec
                                              b@(TBang m (TVar y)) <- new_type
                                              ufold' <- return $ List.map (\(dcon, typ) -> (dcon, subs_typ_var x (TVar y) typ)) ufold'
                                              ufold' <- return $ List.map (\(dcon, typ) -> (dcon, subs_flag n m typ)) ufold'
                                              return (b:a', ufold')) (return ([], ufold)) a

                -- Generate the constraints ufold <: ufold'
                constraints <- List.foldl (\rec ((_, t), (_, u)) -> do
                                             r <- rec
                                             cset <- break_composite False ([t <: u], [])    -- We don't want the user type constraints to be replaced yet
                                             return $ cset <> r) (return emptyset) (List.zip ufold ufold')

                ctx <- get_context
                set_context $ ctx { types = IMap.insert n (Left spec { d_subtype = (a, a', constraints) }) $ types ctx }) (return ()) dblock

  -- Unfold until the constraint set is stable
  unfold_all dblock
  newlog 0 "<<\n"



-- | An auxiliary function used by 'define_user_properties' to check quantum data types. The list of names corresponds to the list
-- of unsolved types. When a user type of this list is encountered, it is added to the list of dependencies, and the data check
-- is delayed until later.
is_qdata_lintype :: LinType -> [Variable] -> QpState (Bool, [Variable])
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
    case spec of
      Left def -> return (d_qdatatype def, deps)
      Right syn -> return (s_qdatatype syn, deps)
  else
    return (b, typename:deps)

is_qdata_lintype _ _ = 
  return (False, [])



-- | An auxiliary function used by 'define_user_properties' to check quantum data types. The list of names corresponds to the list
-- of unsolved types. When a user type of this list is encountered, it is added to the list of dependencies, and the data check
-- is delayed until later.
is_qdata_type :: Type -> [Variable] -> QpState (Bool, [Variable])
is_qdata_type (TBang _ a) names =
  is_qdata_lintype a names 


-- | Input a list of types that satisfy a property, and a graph of consequences. Then the function propagates the
-- property to the dependencies in the graph, modifying the graph in so doing.
propagate_prop :: [Variable] -> IntMap [Variable] -> ([Variable], Bool, IntMap [Variable])
propagate_prop [] graph =
  ([], False, graph)

propagate_prop (n:rest) graph =
  case IMap.lookup n graph of
    Just deps -> 
        let (r', c, g') = propagate_prop (List.union rest deps) (IMap.delete n graph) in
        (n:r', True, g')

    Nothing ->
        let (r', c, g') = propagate_prop rest graph in
        if c then
          propagate_prop (n:r') g'
        else
          (n:r', False, g')


-- | Define the user property: quantum data type. This property can only be defined for all the types taken at the same time.
-- This function first builds a graph of dependencies indicating which type uses which type in the type of the data
-- constructors. Some types are clearly marked as being non quantum data types. In the graph of dependencies, all the types
-- using these non-quantum types cannot in turn be quantum data types; and so on. After all the non quantum data types have been eliminated,
-- all that remain are quantum data types.
define_user_properties :: [Variable] -> QpState ()
define_user_properties dblock = do
  -- A specific function is needed to check quantum data types
    newlog 0 ">> User type properties"

    -- Creates the map of dependencies of quantum data type properties
    -- The edges are oriented so that if one of the types doesn't have a property, then neither should the dependencies.
    (mdata, mgraph) <- List.foldl (\rec n -> do
                         (mdata, mgraph) <- rec
                         Left spec <- type_spec n
                         -- Replace the arguments by qubit in the unfolded definition
                         argtyps <- return $ List.map (\(_, argtyp) ->
                                                         List.foldl (\a (TBang _ t) ->
                                                                      case t of
                                                                        TVar x -> subs_typ_var x TQubit a
                                                                        _ -> throw $ ProgramError "define_user_properties"
                                                                    ) argtyp $ fst $ d_unfolded spec) (snd $ d_unfolded spec)
                         -- Check each of the types for quantum data types
                         (b, deps) <- List.foldl (\rec a -> do
                                                    (b, deps) <- rec
                                                    if b then do
                                                      (b', deps') <- is_qdata_type a dblock
                                                      return (b', List.union deps' deps)
                                                    else
                                                      return (False, [])) (return (True, [])) argtyps

                         -- Increase the map
                         if b then do
                           return (mdata, List.foldl (\m d ->
                                                        case IMap.lookup d m of
                                                          Just l -> IMap.insert d (n:l) m
                                                          Nothing -> IMap.insert d [n] m) mgraph deps)
                         else do
                           return (n:mdata, mgraph)) (return ([], IMap.empty)) dblock

    -- Solve the map, and set the quantum data properties
    (mdata', _, _) <- return $ propagate_prop mdata mgraph
    List.foldl (\rec n -> do
                  rec
                  if List.elem n mdata' then do
                    -- Not a quantum data type
                    newlog 0 $ "-- " ++ show n ++ " is not a quantum data type"
                    ctx <- get_context
                    Left spec <- type_spec n
                    set_context $ ctx { types = IMap.insert n (Left spec { d_qdatatype = False }) $ types ctx }
                  else do
                    -- Quantum data type
                    newlog 0 $ "-- " ++ show n ++ " may be a quantum data type"
                    -- Since the default value is True, no need to set it here)
                    return ()) (return ()) dblock
                

    newlog 0 "<<\n"




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

    -- The variable is a user type, either algebraic type or type synonym.
    Just (TBang _ (TUser id as)) -> do
        spec <- type_spec id
        nexp <- case spec of
                  Left def -> return $ d_args def
                  Right syn -> return $ s_args syn
        nact <- return $ (List.length as) + (List.length arg)

        if nexp == nact then do
          n <- fresh_flag
          return (TBang n $ TUser id (as ++ arg), label)
        else do
          ex <- get_location
          throw $ LocatedError (WrongTypeArguments x nexp nact) ex

    -- The variable is just a bound type.
    Just typ ->
        if arg == [] then
          return (typ, label)
        else do
          ex <- get_location
          throw $ LocatedError (WrongTypeArguments (pprint typ) 0 (List.length arg)) ex

    -- If the variable is not found, it can be a free variable (depending on the boolean arg)
    Nothing -> do
        if bound then do
          -- If the type variables are supposed to be bound, this one isn't.
          ex <- get_location
          throw $ LocatedError (UnboundVariable x) ex

        else do
          -- Last case, if the type authorize free variables, register this one with a new type
          t <- new_type
          return (t, Map.insert x t label)



translate_type (S.TQualified m x) arg lbl = do
  id <- lookup_qualified_type (m, x)
  spec <- type_spec id
  -- Expected number of args
  nexp <- case spec of
            Left def -> return $ d_args def
            Right syn -> return $ s_args syn
  -- Actual number of args
  nact <- return $ List.length arg

  if nexp == nact then do
    n <- fresh_flag
    return (TBang n (TUser id arg), fst lbl)
  else do
    ex <- get_location
    throw $ LocatedError (WrongTypeArguments x nexp nact) ex

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

-- Remaining cases: of types applied to an argument when they are not generic
translate_type t args label = do
  ex <- get_location
  throw $ LocatedError (WrongTypeArguments (pprint t) 0 (List.length args)) ex



-- | Apply the function 'Typing.TransSyntax.translate_type' to a bound type.
-- The arguments must be null initially.
translate_bound_type :: S.Type -> LabellingContext -> QpState Type
translate_bound_type t label = do
  (t', _) <- translate_type t [] (l_types label, True)
  return t'



-- | Apply the function 'Typing.TransSyntax.translate_type' to unbound types.
-- The binding map is initially empty, and is dropped after the translation of the type.
-- No argument is passed to the top type.
translate_unbound_type :: S.Type -> LabellingContext -> QpState Type
translate_unbound_type t label = do
  (t', _) <- translate_type t [] (l_types label, False)
  return t'



-- | Translate a pattern, given a labelling map.
-- The map is updated as variables are bound in the pattern.
translate_pattern :: S.Pattern -> LabellingContext -> QpState (Pattern, Map String LVariable)
translate_pattern S.PUnit label = do
  return (PUnit, l_variables label)

translate_pattern (S.PBool b) label = do
  return (PBool b, l_variables label)

translate_pattern (S.PInt n) label = do
  return (PInt n, l_variables label)

translate_pattern S.PWildcard label = do
  return (PWildcard, l_variables label)

translate_pattern (S.PVar x) label = do
  ex <- get_location
  id <- register_var x ex
  return (PVar id, Map.insert x (LVar id) $ l_variables label)

translate_pattern (S.PTuple plist) label = do
  (plist', lbl) <- List.foldr (\p rec -> do
                                  (r, lbl) <- rec
                                  (p', lbl') <- translate_pattern p $ label { l_variables = lbl }
                                  return ((p':r), lbl')) (return ([], l_variables label)) plist
  return (PTuple plist', lbl)

translate_pattern (S.PDatacon datacon p) label = do
  case Map.lookup datacon $ l_datacons label of
    Just id -> do
        case p of
          Just p -> do
              (p', lbl) <- translate_pattern p label
              return (PDatacon id (Just p'), lbl)

          Nothing ->
              return (PDatacon id Nothing, l_variables label)

    Nothing ->
        throw_UnboundDatacon datacon

translate_pattern (S.PLocated p ex) label = do
  set_location ex
  (p', lbl) <- translate_pattern p label
  return (PLocated p' ex, lbl)


translate_pattern (S.PConstraint p t) label = do
  (p', lbl) <- translate_pattern p label
  return (PConstraint p' (t, l_types label), lbl)



-- | Translate an expression, given a labelling map.
translate_expression :: S.Expr -> LabellingContext -> QpState Expr
translate_expression (S.EWildcard a) _ = S.absurd a

translate_expression S.EUnit _ = do
  return EUnit

translate_expression (S.EBool b) _ = do
  return (EBool b)

translate_expression (S.EInt n) _ = do
  return (EInt n)

translate_expression (S.EVar x) label = do
  case Map.lookup x $ l_variables label of
    Just (LVar v) -> do
        return (EVar v)

    Just (LGlobal v) -> do
        return (EGlobal v)

    Nothing -> do
        throw_UnboundVariable x

translate_expression (S.EQualified m x) _ = do
  id <- lookup_qualified_var (m, x)
  return $ EGlobal id

translate_expression (S.EFun p e) label = do
  (p', lbl) <- translate_pattern p label
  e' <- translate_expression e $ label { l_variables = lbl }
  return (EFun p' e')

translate_expression (S.ELet r p e f) label = do
  (p', lbl) <- translate_pattern p label
  case r of
    Recursive -> do
        e' <- translate_expression e $ label { l_variables = lbl }
        f' <- translate_expression f $ label { l_variables = lbl }
        return (ELet r p' e' f')

    Nonrecursive -> do
        e' <- translate_expression e label
        f' <- translate_expression f $ label { l_variables = lbl }
        return (ELet r p' e' f')

translate_expression (S.EDatacon datacon e) label = do
  case Map.lookup datacon $ l_datacons label of
    Just id -> do
        case e of
          Just e -> do
              e' <- translate_expression e label
              return (EDatacon id $ Just e')

          Nothing ->
              return (EDatacon id Nothing)

    Nothing -> do
        throw_UnboundDatacon datacon

translate_expression (S.EMatch e blist) label = do
  e' <- translate_expression e label
  blist' <- List.foldr (\(p, f) rec -> do
                          r <- rec
                          (p', lbl) <- translate_pattern p label
                          f' <- translate_expression f $ label { l_variables = lbl }
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

translate_expression (S.EBox t) label = do
  ex <- get_location
  t' <- translate_bound_type t label
  -- Check that the type of the box is a quantum data type
  qdata <- Q.is_qdata_type t'
  if not qdata then do
    prt <- pprint_type_noref t'
    throwQ $ LocatedError (BoxTypeError prt) ex

  else
    -- The translation of the type of the box in the core syntax produces
    -- some constraints that needs to be conveyed to the type inference
    -- Using a scheme is a way of doing it
    return (EBox t')

translate_expression S.EUnbox _ = do
  return EUnbox

translate_expression S.ERev _ = do
  return ERev

translate_expression (S.ELocated e ex) label = do
  set_location ex
  e' <- translate_expression e label
  return $ ELocated e' ex

translate_expression (S.EBuiltin s) _ = do
  -- Check the existence of the built-in value before translating it
  ctx <- get_context
  if Map.member s $ builtins ctx then
    -- Ok, the built-in s exists
    return $ EBuiltin s
  else do
    -- Wrong, no built-in of name s has been defined
    ex <- get_location
    throwQ $ LocatedError (UndefinedBuiltin s) ex

translate_expression (S.EConstraint e t) label = do
  e' <- translate_expression e label
  return $ EConstraint e' (t, l_types label)



-- | If an interface file is provided, modify the pattern by adding type constraints corresponding to the types
-- written in the interface.
with_interface :: S.Program -> LabellingContext -> Pattern -> QpState Pattern
with_interface _ _ PWildcard =
  return PWildcard

with_interface _ _ PUnit =
  return PUnit

with_interface _ _ (PBool b) =
  return (PBool b)

with_interface _ _ (PInt n) =
  return (PInt n)

with_interface prog label (PLocated p _) =
  with_interface prog label p

with_interface prog label (PVar x) = do
  case S.interface prog of
    Just inter -> do
        -- If an interface file is present, check the presence of the variable x
        n <- variable_name x
        case List.lookup n inter of
          Just typ -> do
              return $ PConstraint (PVar x) (typ, l_types label)
          Nothing -> do
              return $ PVar x
    Nothing -> do
        return $ PVar x

with_interface prog _ (PDatacon dcon Nothing) =
  return $ PDatacon dcon Nothing

with_interface prog label (PDatacon dcon (Just p)) = do
  p' <- with_interface prog label  p
  return $ PDatacon dcon $ Just p'

with_interface prog label (PTuple plist) = do
  plist' <- List.foldr (\p rec -> do
                          r <- rec
                          p' <- with_interface prog label p
                          return (p':r)) (return []) plist
  return $ PTuple plist

with_interface prog label (PConstraint p t) = do
  p' <- with_interface prog label  p
  return (PConstraint p' t)

-- $ All the following functions serve to translate the program implementation and
-- types into the Proto-Quipper core, meaning without all the syntactic sugar.


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

    _ -> do
      throw $ ProgramError "unfold_tensors_in_lintype: illegal tensor"
      
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


-- | Like 'unfold_tensors_in_lintype', but for types.
unfold_tensors :: Type -> QpState Type
unfold_tensors (TBang n a) = do
  a' <- unfold_tensors_in_lintype a
  return $ TBang n a'


-- | Transform a pattern \<a, b, c, d\> into \<a, \<b, \<c, d\>\>\>.
unfold_tuples :: Pattern -> Pattern
unfold_tuples PWildcard =
  PWildcard

unfold_tuples (PLocated p ex) =
  PLocated (unfold_tuples p) ex

unfold_tuples PUnit =
  PUnit

unfold_tuples (PBool b) =
  PBool b

unfold_tuples (PInt n) =
  PInt n

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

    _ ->
        throw $ ProgramError "unfold_tuples: illegal tuple"
        
unfold_tuples (PConstraint p t) = 
  throw $ ProgramError "unfold_tuples: PConstraint not implemented"

-- | Remove the syntactic sugar from an expression.
-- This function operates on core expressions. As syntactic sugar is removed, new variables are
-- produced.
desugar :: Expr -> QpState Expr

desugar (EVar x) =
  return $ EVar x

desugar (EGlobal x) =
  return $ EGlobal x

desugar (EFun p e) = do
   -- Check whether the expression is already desugared or not
  case p of
    -- The pattern is only one variable: do nothing
    PVar _ -> do
      e' <- desugar e
      return $ EFun p e'

    -- If the pattern is more complicated, replace it by a variable
    _ -> do
      x <- dummy_var
      e' <- desugar $ ELet Nonrecursive p (EVar x) e
      return $ EFun (PVar x) e'

desugar (EApp e f) = do
  e' <- desugar e
  f' <- desugar f
  return $ EApp e' f'

desugar EUnit = do
  return EUnit

-- Tuples are a syntactic sugar for chained pairs :
-- the tuple <a, b, c, d> is the pattern <a, <b, <c, d>>>
desugar (ETuple elist) = do
  case elist of
    -- This is the minimum size tuple, and is left as is
    [e,f] -> do
        e' <- desugar e
        f' <- desugar f
        return $ ETuple [e', f']

    -- With more elements: desugar the rest, and 'append' the head on the left
    (e:rest) -> do
        e' <- desugar e
        rest' <- desugar $ ETuple rest
        return $ ETuple [e', rest']

    -- The other cases of empty and sinleton tuples shouldn't appear
    _ -> throw $ ProgramError "desugar: illegal tuple"

desugar (ELet r p e f) = do
  p' <- return $ unfold_tuples p
  e' <- desugar e
  case p' of
    -- If the pattern is unit: do nothing
    PUnit -> do
        f' <- desugar f
        return $ ELet r p' e' f'

    -- If the pattern is boolean: do nothing
    (PBool b) -> do
        f' <- desugar f
        return $ ELet r p' e' f'

    -- If the pattern is an integer: do nothing
    (PInt n) -> do
        f' <- desugar f
        return $ ELet r p' e' f'

    -- If the pattern is one variable, do nothing
    -- The let binding can't be removed because of let-polymorphism
    PVar _ -> do
        f' <- desugar f
        return $ ELet r p' e' f'

    -- If the pattern is a pair of variables, this is the case of tensor elimination
    PTuple [PVar _, PVar _] -> do
        f' <- desugar f
        return $ ELet r p' e' f'

    -- If one of the elements of the pattern is not a variable, desugar
    PTuple [PVar x, q] -> do
        y <- dummy_var
        f' <- desugar $ ELet r q (EVar y) f
        return $ ELet r (PTuple [PVar x, PVar y]) e' f'

    PTuple [p, PVar x] -> do
        y <- dummy_var
        f' <- desugar $ ELet r p (EVar y) f
        return $ ELet r (PTuple [PVar y, PVar x]) e' f'

    PTuple [p, q] -> do
        x <- dummy_var
        y <- dummy_var
        f' <- desugar $ ELet r p (EVar x) (ELet r q (EVar y) f)
        return $ ELet Nonrecursive (PTuple [PVar x, PVar y]) e' f'

    -- If the pattern is a datacon, desugar by adding a pattern matching
    PDatacon dcon Nothing -> do
        f' <- desugar f
        return $ EMatch e' [(PDatacon dcon Nothing, f')]

    PDatacon dcon (Just p) -> do
        case p of
          PVar x -> do
              f' <- desugar f
              return $ EMatch e' [(PDatacon dcon $ Just p, f')]

          _ -> do
              x <- dummy_var
              f' <- desugar (ELet Nonrecursive p (EVar x) f)
              return $ EMatch e' [(PDatacon dcon $ Just (PVar x), f')]

    _ -> return $ ELet r p e f

desugar (EBool b) = do
  return $ EBool b

desugar (EInt n) = do
  return $ EInt n

desugar (EIf e f g) = do
  e' <- desugar e
  f' <- desugar f
  g' <- desugar g
  return $ EIf e' f' g'

desugar (EDatacon dcon Nothing) = do
  return $ EDatacon dcon Nothing

desugar (EDatacon dcon (Just e)) = do
  e' <- desugar e
  return $ EDatacon dcon $ Just e'

desugar (EMatch e blist) = do
  e' <- desugar e
  blist' <- List.foldr aux (return []) blist
  return $ EMatch e' blist'
    where 
      aux (p, f) rec = do
        r <- rec
        case p of
          PDatacon dcon Nothing -> do
            f' <- desugar f
            return $ (PDatacon dcon Nothing, f'):r

          PDatacon dcon (Just p) -> do
            x <- dummy_var
            f' <- desugar $ ELet Nonrecursive p (EVar x) f
            return $ (PDatacon dcon $ Just (PVar x), f'):r
                            
          -- The other cases are ignored for now, as syntactic equality hasn't been developed yet
          _ -> throw $ ProgramError "desugar:EMatch: unimplemented case"

desugar (EBox typ) = do
  return $ EBox typ

desugar EUnbox = do
  return EUnbox

desugar ERev = do
  return ERev

desugar (ELocated e ex) = do
  e' <- desugar e
  return $ ELocated e' ex 

desugar (EBuiltin s) =
  return (EBuiltin s)
  
desugar (EConstraint e t) =
  return (EConstraint e t)
