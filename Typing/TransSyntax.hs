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
  import_typedefs,
  import_typesyn) where

import Utils
import Classes
import Builtins

import Typing.CoreSyntax
import Typing.LabellingContext (LabellingContext, empty_label, LVariable (..))
import qualified Typing.LabellingContext as L
import Typing.CorePrinter
import Typing.Subtyping

import Parsing.Location
import qualified Parsing.Syntax as S
import Parsing.Printer

import Interpret.Values
import Interpret.Circuits as C

import qualified Compiler.SimplSyntax as CS

import Monad.QuipperError
import Monad.QpState hiding (is_qdata_lintype, is_qdata_type)
import qualified Monad.QpState as Q (is_qdata_lintype, is_qdata_type)
import Monad.Modules (Module)
import qualified Monad.Modules as M

import Data.Map as Map
import qualified Data.List as List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap




-- | Import the type definitions in the current state.
-- The data constructors are labelled during this operation, their associated type translated, and themselves included in the field datacons of the state.
import_typedefs :: [S.Typedef]                -- ^ A block of co-inductive type definitions.
                -> LabellingContext           -- ^ The current labelling context.
                -> QpState LabellingContext   -- ^ The updated labelling context.
import_typedefs dblock label = do
  -- Import the type definitions.
  -- At first, the definition is empty, it will be elaborated later.
  -- The types of the block are added to the labelling map: this is what allows for co-inductive types
  (typs, names) <- List.foldl (\rec def@(S.Typedef typename args _) -> do
        (typs, names) <- rec
        spec <- return $ Typedef {
              d_args = List.length args,
              d_qdatatype = True,            -- qdata type by default
              d_unfolded = ([], []),
              d_subtype = ([], [], emptyset),
              d_gettag = \x -> CS.EVar x
            }

        -- Register the type in the current context
        id <- register_typedef typename spec
        -- Add the type in the map
        return (Map.insert typename (TBang 0 $ TAlgebraic id []) typs, id:names)) (return (L.types label, [])) dblock

  -- Transcribe the rest of the type definitions.
  -- Type definitions include: the name of the type, generic variables, the list of constructors
  datas <- List.foldl (\rec (S.Typedef typename args dlist) -> do
        lbl <- rec
        -- Type id needed for udpates.
        typeid <- case Map.lookup typename typs of
            Just (TBang _ (TAlgebraic id _)) -> return id
            _ -> fail "TransSyntax:import_typedefs: unexpected non-algebraic type"

        -- Bind the arguments of the type.
        -- For each string argument a, a type !n a is created and bound in the map mapargs.
        (args', mapargs) <- List.foldr (\a rec -> do
              (args, m) <- rec
              ta <- new_type
              return (ta:args, Map.insert a ta m)) (return ([], typs)) args

        -- Define the type of the data constructors
        (dtypes', m) <- List.foldl (\rec (no, (dcon, dtype)) -> do
              (dt, lbl) <- rec
              (dtype, argtyp, cset) <- case dtype of
                    -- If the constructor takes no argument
                    Nothing -> do
                        m <- fresh_flag
                        return (TBang m (TAlgebraic typeid args'), Nothing, emptyset)

                    -- If the constructor takes an argument
                    Just dt -> do
                        dt'@(TBang n _) <- translate_bound_type dt $ empty_label { L.types = mapargs }
                        m <- fresh_flag
                        return (TBang one (TArrow dt' (TBang m $ TAlgebraic typeid args')), Just dt', ([], [Le m n no_info]))

              -- Generalize the type of the constructor over the free variables and flags
              -- Those variables must also respect the constraints from the construction of the type
              (fv, ff) <- return (free_typ_var dtype, free_flag dtype)
              dtype <- return $ TForall ff fv cset dtype

              -- Register the datacon
              id <- register_datacon dcon $ Datacondef {
                    d_type = dtype,
                    d_datatype = typeid,
                    d_tag = no,
                    d_ref = -1,
                    d_construct = Left CS.EUnit,
                    d_deconstruct = \x -> CS.EVar x
                  }
              return $ ((id, argtyp):dt, Map.insert dcon id lbl)) (return ([], lbl)) (List.zip [0..(List.length dlist)-1] dlist)

        -- Update the specification of the type
        spec <- algebraic_def typeid
        ctx <- get_context
        set_context $ ctx { algebraics = IMap.insert typeid spec { d_unfolded = (args', dtypes') } $ algebraics ctx }

        -- Specify the implementation of this type
        choose_implementation typeid

        return m) (return $ L.datacons label) dblock



  -- Infer the properties of the user types
  define_user_subtyping names
  define_user_properties names

  -- Return the updated labelling map for types, and the map for dataconstructors.
  return $ label { L.datacons = datas,
                   L.types = typs }



-- | Settle the implementation (machine representation) of all the constructors of an algebraic type.
choose_implementation :: Algebraic -> QpState ()
choose_implementation typ = do
  dtyp <- algebraic_def typ
  let datas = snd $ d_unfolded dtyp
  ctx <- get_context
  case datas of
    -- Cases with one constructor:
    -- The tag is omitted. No definition of the function gettag is needed. 
    [(dcon, Just _)] -> do
        update_datacon dcon (\ddef -> Just ddef { d_construct = Right (\e -> e), d_deconstruct = \v -> CS.EVar v })
        
    [(dcon, Nothing)] ->
        update_datacon dcon (\def -> Just def { d_construct = Left $ CS.EInt 0, d_deconstruct = \v -> CS.EInt 0 })
        
    -- Cases with several constrcutors
    _ -> do
        -- First thing : count the constructors taking an argument.
        let (with_args, no_args) = List.partition ((/= Nothing) . snd) datas

        -- In case at most one takes an argument, the remaining can be represented by just their tag.
        if List.length with_args <= 1 then do
          -- The constructor with one argument can forget its tag
          List.foldl (\rec (dcon, _) -> do
                rec
                update_datacon dcon (\ddef -> Just ddef { d_construct = Right (\e -> CS.ETuple [e]), d_deconstruct = \v -> CS.EAccess 0 v })
              ) (return ()) with_args
          -- The constructors with no argument are represented by just their tag. The deconstruct function is not needed.
          List.foldl (\rec (dcon, _) -> do
                rec
                update_datacon dcon (\ddef -> Just ddef { d_construct = Left $ CS.EInt (d_tag ddef) })
              ) (return ()) no_args
          -- The tag is obtained by checking for references.
          case with_args of
            -- Since there isn't any reference in the lot, no need to check
            [] -> update_algebraic typ (\tdef -> Just tdef { d_gettag = \v -> CS.EVar v })
            -- There is a reference: need to check
            [(dcon, _)] -> do
                tag <- datacon_def dcon >>= return . d_tag
                update_algebraic typ (\tdef -> Just tdef { d_gettag = \v -> CS.EIf (CS.EApp (CS.EBuiltin "ISREF") (CS.EVar v))
                                                                       (CS.EInt tag)
                                                                       (CS.EVar v) })
            _ ->
                fail "TransSyntax:choose_implementation: unexpected case"

        -- If not, just give the default implementation.
        else do
          -- The constructor with one argument can forget its tag
          List.foldl (\rec (dcon, _) -> do
                rec
                update_datacon dcon (\ddef -> Just ddef { d_construct = Right (\e -> CS.ETuple [CS.EInt (d_tag ddef),e]), d_deconstruct = \v -> CS.EAccess 1 v })
              ) (return ()) with_args
          -- The constructors with no argument are represented by just their tag. The deconstruct function is not needed.
          List.foldl (\rec (dcon, _) -> do
                rec
                update_datacon dcon (\ddef -> Just ddef { d_construct = Left $ CS.ETuple [CS.EInt (d_tag ddef)] })
              ) (return ()) no_args
          -- The tag is the first element of the tuple.
          update_algebraic typ (\tdef -> Just tdef { d_gettag = \v -> CS.EAccess 0 v })



-- | Unfold the definitions of the types in the subtyping constraints
-- products of the reduction of user a <: user a'
-- Takes the name of the type as input, and returns the resulting set.
-- No modification is made to the specification of the type.
unfold_once :: Algebraic -> QpState ConstraintSet
unfold_once name = do
  spec <- algebraic_def name
  
  -- Unfolded constraints
  (a, a', current) <- return $ d_subtype spec
  
  -- unfold the user type constraints
  cuser <- unfold_algebraic_constraints_in_set current

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
unfold_all :: [Algebraic] -> QpState ()
unfold_all [] = return ()
unfold_all names = do
  -- Get all the specifications
  specs <- List.foldr (\n rec -> do 
        r <- rec
        s <- algebraic_def n
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
        let (a, a', subt) = d_subtype spec
        let before = (List.filter (not . is_algebraic) (fst subt), snd subt)
        let (cuser, cnuser) =
              let (lc, lc') = List.partition is_algebraic (fst after) in
              (lc, (lc', snd after))

        -- Check the stability of the non user constraints of before and after the unfolding
        if before `equals_set` cnuser then do
          -- Terminate the recursion, and retain in the subtyping of n only the non user constraints
          newlog 0 ("[" ++ List.foldl (\rec c -> " " ++ pprint c ++ rec) "" (fst before) ++ 
                           List.foldl (\rec c -> " " ++ pprint c ++ rec) "" (snd before) ++ " ] => " ++
                    pprint (TAlgebraic n a) ++ " <: " ++ pprint (TAlgebraic n a'))

          return (b, ctx { algebraics = IMap.insert n spec { d_subtype = (a, a', before) } $ algebraics ctx })
        else do
          -- Continue the recursion, but update the subtyping of n
          return (n:b, ctx { algebraics = IMap.insert n spec { d_subtype = (a, a', after) } $ algebraics ctx })) (return ([], ctx)) (List.zip3 names specs unfolded) 

  -- Continue or not with the recursion
  set_context ctx
  unfold_all finish



-- | Infer the subtyping relation rules of all the user defined types.
-- It uses the algorithm described above.
define_user_subtyping :: [Algebraic] -> QpState () 
define_user_subtyping dblock = do
  newlog 0 ">> User subtyping relations"

  -- Initialize the constraint set of each user type
  List.foldl (\rec n -> do
        rec
        spec <- algebraic_def n
        -- One version of the unfolded type
        let (a, ufold) = d_unfolded spec
         
        -- Another version of the unfolded type, where a has been replaced by fresh types a'
        (a', ufold') <- List.foldr (\(TBang n t) rec -> do
              let x = unTVar t
              (a', ufold') <- rec
              b@(TBang m (TVar y)) <- new_type
              ufold' <- return $ List.map (\(dcon, typ) -> (dcon, typ >>= (\t -> Just $ subs_typ_var x (TVar y) t))) ufold'
              ufold' <- return $ List.map (\(dcon, typ) -> (dcon, typ >>= (\t -> Just $ subs_flag n m t))) ufold'
              return (b:a', ufold')) (return ([], ufold)) a

        -- Generate the constraints ufold <: ufold'
        constraints <- List.foldl (\rec ((_, t), (_, u)) -> do
              r <- rec
              case (t, u) of
                (Just t, Just u) -> do
                    cset <- break_composite False ([t <: u], [])    -- We don't want the user type constraints to be replaced yet
                    return $ cset <> r
                _ ->
                    return r) (return emptyset) (List.zip ufold ufold')

        ctx <- get_context
        set_context $ ctx { algebraics = IMap.insert n spec { d_subtype = (a, a', constraints) } $ algebraics ctx }) (return ()) dblock

  -- Unfold until the constraint set is stable
  unfold_all dblock
  newlog 0 "<<\n"
    where
      unTVar (TVar x) = x
      unTVar _ = throwNE $ ProgramError "TransSyntax:define_user_subtyping: unexpected non-atomic constraint"



-- | Translate and import a type synonym.
import_typesyn :: S.Typesyn                   -- ^ A type synonym.
               -> LabellingContext            -- ^ The current labelling context.
               -> QpState LabellingContext    -- ^ The updated labelling context.
import_typesyn typesyn label = do
  -- Count the arguments
  let nargs = List.length $ S.s_args typesyn

  -- map the arguments to core types
  as <- new_types nargs
  let margs = Map.fromList $ List.zip (S.s_args typesyn) as

  -- Translate the synonym type
  syn <- translate_bound_type (S.s_synonym typesyn) (label { L.types = Map.union margs $ L.types label }) 

  -- Is it a quantum data type ?
  qdata <- Q.is_qdata_type syn

  -- Build the type specification
  spec <- return $ Typesyn {
        s_args = nargs,
        s_qdatatype = qdata,
        s_unfolded = (snd $ List.unzip $ Map.assocs margs, syn) }

  -- Register the type synonym
  id <- register_typesyn (S.s_typename typesyn) spec

  -- Add the type to the labelling context and return
  return label { L.types = Map.insert (S.s_typename typesyn) (TBang 0 $ TSynonym id []) $ L.types label }




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
is_qdata_lintype (TAlgebraic typename args) names = do
  -- Check the type of the arguments
  (b, deps) <- List.foldl (\rec t -> do
                             (b, deps) <- rec
                             if b then do
                               (b', deps') <- is_qdata_type t names
                               return (b', List.union deps deps')
                             else
                               return (False, [])) (return (True, [])) args
  -- If the arguments are ok, check the type (iff it is not in the list)
  if b && (not $ List.elem typename names) then do
    spec <- algebraic_def typename
    return (d_qdatatype spec, deps)
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
                         spec <- algebraic_def n
                         -- Replace the arguments by qubit in the unfolded definition
                        
                         let argtyps = List.foldl (\args (_, typ) -> do
                                case typ of
                                  Nothing -> args
                                  Just t ->
                                    let t' = List.foldl (\t a -> subs_typ_var (unTVar a) TQubit t) t (fst $ d_unfolded spec) in
                                    t':args) [] (snd $ d_unfolded spec)
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
                    spec <- algebraic_def n
                    set_context $ ctx { algebraics = IMap.insert n spec { d_qdatatype = False } $ algebraics ctx }
                  else do
                    -- Quantum data type
                    newlog 0 $ "-- " ++ show n ++ " may be a quantum data type"
                    -- Since the default value is True, no need to set it here)
                    return ()) (return ()) dblock
                

    newlog 0 "<<\n"
    where
      unTVar (TBang _ (TVar x)) = x
      unTVar _ = throwNE $ ProgramError "TransSyntax:define_user_properties: unexpected non-variable argument"



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
        let nexp = d_args spec
        nact <- return $ (List.length as) + (List.length arg)

        if nexp == nact then do
          n <- fresh_flag
          return (TBang n $ TAlgebraic id (as ++ arg), label)
        else do
          ex <- get_location
          throwQ (WrongTypeArguments x nexp nact) ex

    -- The variable is a type synonym.
    Just (TBang _ (TSynonym id as)) -> do
        spec <- synonym_def id
        let nexp = s_args spec
        nact <- return $ (List.length as) + (List.length arg)

        if nexp == nact then do
          n <- fresh_flag
          return (TBang n $ TAlgebraic id (as ++ arg), label)
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
          return $ d_args dalg
        TBang _ (TSynonym syn _) -> do
          dsyn <- synonym_def syn
          return $ s_args dsyn
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
-- The second argument indicates whether the pattern is from a top level declaration or not.
translate_pattern :: S.Pattern -> Bool -> LabellingContext -> QpState (Pattern, Map String LVariable)
translate_pattern S.PUnit _ label = do
  ref <- create_ref
  update_ref ref (\ri -> Just ri { r_expression = Right $ PUnit ref })
  return (PUnit ref, L.variables label)

translate_pattern (S.PBool b) _ label = do
  ref <- create_ref
  update_ref ref (\ri -> Just ri { r_expression = Right $ PBool ref b })
  return (PBool ref b, L.variables label)

translate_pattern (S.PInt n) _ label = do
  ref <- create_ref
  update_ref ref (\ri -> Just ri { r_expression = Right $ PInt ref n })
  return (PInt ref n, L.variables label)

translate_pattern S.PWildcard _ label = do
  ref <- create_ref
  update_ref ref (\ri -> Just ri { r_expression = Right $ PWildcard ref })
  return (PWildcard ref, L.variables label)

translate_pattern (S.PVar x) toplevel label = do
  ref <- create_ref
  id <- register_var x ref
  update_ref ref (\ri -> Just ri { r_expression = Right $ PVar ref id })
  return (PVar ref id, Map.insert x (if toplevel then LGlobal id else LVar id) $ L.variables label)

translate_pattern (S.PTuple plist) toplevel label = do
  ref <- create_ref
  (plist', lbl) <- List.foldr (\p rec -> do
                                  (r, lbl) <- rec
                                  (p', lbl') <- translate_pattern p toplevel label { L.variables = lbl }
                                  return ((p':r), lbl')) (return ([], L.variables label)) plist
  update_ref ref (\ri -> Just ri { r_expression = Right $ PTuple ref plist' })
  return (PTuple ref plist', lbl)

translate_pattern (S.PDatacon datacon p) toplevel label = do
  ref <- create_ref
  case Map.lookup datacon $ L.datacons label of
    Just id -> do
        case p of
          Just p -> do
              (p', lbl) <- translate_pattern p toplevel label
              update_ref ref (\ri -> Just ri { r_expression = Right $ PDatacon ref id (Just p') })
              return (PDatacon ref id (Just p'), lbl)

          Nothing -> do
              update_ref ref (\ri -> Just ri { r_expression = Right $ PDatacon ref id Nothing })
              return (PDatacon ref id Nothing, L.variables label)

    Nothing ->
        throw_UnboundDatacon datacon

translate_pattern (S.PLocated p ex) toplevel label = do
  set_location ex
  translate_pattern p toplevel label

translate_pattern (S.PConstraint p t) toplevel label = do
  (p', lbl) <- translate_pattern p toplevel label
  return (PConstraint p' (t, L.types label), lbl)



-- | Translate an expression, given a labelling map.
translate_expression :: S.Expr -> LabellingContext -> QpState Expr
translate_expression (S.EWildcard a) _ = S.absurd a

translate_expression S.EUnit _ = do
  ref <- create_ref
  update_ref ref (\ri -> Just ri { r_expression = Left $ EUnit ref })
  return (EUnit ref)

translate_expression (S.EBool b) _ = do
  ref <- create_ref
  update_ref ref (\ri -> Just ri { r_expression = Left $ EBool ref b })
  return (EBool ref b)

translate_expression (S.EInt n) _ = do
  ref <- create_ref
  update_ref ref (\ri -> Just ri { r_expression = Left $ EInt ref n })
  return (EInt ref n)

translate_expression (S.EVar x) label = do
  ref <- create_ref
  case Map.lookup x $ L.variables label of
    Just (LVar v) -> do
        update_ref ref (\ri -> Just ri { r_expression = Left $ EVar ref v })
        return (EVar ref v)

    Just (LGlobal v) -> do
        update_ref ref (\ri -> Just ri { r_expression = Left $ EGlobal ref v })
        return (EGlobal ref v)

    Nothing -> do
        throw_UnboundVariable x

translate_expression (S.EQualified m x) _ = do
  ref <- create_ref
  id <- lookup_qualified_var (m, x)
  update_ref ref (\ri -> Just ri { r_expression = Left $ EGlobal ref id })
  return $ EGlobal ref id

translate_expression (S.EFun p e) label = do
  ref <- create_ref
  (p', lbl) <- translate_pattern p False label
  e' <- translate_expression e $ label { L.variables = lbl }
  update_ref ref (\ri -> Just ri { r_expression = Left $ EFun ref p' e' })
  return (EFun ref p' e')

translate_expression (S.ELet r p e f) label = do
  ref <- create_ref
  (p', lbl) <- translate_pattern p False label
  e' <- case r of
        Recursive -> do
            translate_expression e $ label { L.variables = lbl }
        Nonrecursive -> do
            translate_expression e $ label
  f' <- translate_expression f $ label { L.variables = lbl }
  update_ref ref (\ri -> Just ri { r_expression = Left $ ELet ref r p' e' f' })
  return (ELet ref r p' e' f')

translate_expression (S.EDatacon datacon e) label = do
  ref <- create_ref
  case Map.lookup datacon $ L.datacons label of
    Just id -> do
        case e of
          Just e -> do
              e' <- translate_expression e label
              update_ref ref (\ri -> Just ri { r_expression = Left $ EDatacon ref id $ Just e' })
              return (EDatacon ref id $ Just e')

          Nothing -> do
              update_ref ref (\ri -> Just ri { r_expression = Left $ EDatacon ref id Nothing })
              return (EDatacon ref id Nothing)

    Nothing -> do
        throw_UnboundDatacon datacon

translate_expression (S.EMatch e blist) label = do
  ref <- create_ref
  e' <- translate_expression e label
  blist' <- List.foldr (\(p, f) rec -> do
                          r <- rec
                          (p', lbl) <- translate_pattern p False label
                          f' <- translate_expression f $ label { L.variables = lbl }
                          return ((p', f'):r)) (return []) blist
  update_ref ref (\ri -> Just ri { r_expression = Left $ EMatch ref e' blist' })
  return (EMatch ref e' blist')

-- Convert the application of a data constructor to a data constrcutor with an argument.
translate_expression (S.EApp (S.ELocated (S.EDatacon dcon Nothing) _) e) label = do
  ref <- create_ref
  e' <- translate_expression e label
  case Map.lookup dcon $ L.datacons label of
    Just id -> do
        update_ref ref (\ri -> Just ri { r_expression = Left $ EDatacon ref id $ Just e' })
        return (EDatacon ref id $ Just e')
    Nothing -> do
        throw_UnboundDatacon dcon

translate_expression (S.EApp e f) label = do
  ref <- create_ref
  e' <- translate_expression e label
  f' <- translate_expression f label
  update_ref ref (\ri -> Just ri { r_expression = Left $ EApp ref e' f' })
  return (EApp ref e' f')

translate_expression (S.ETuple elist) label = do
  ref <- create_ref
  elist' <- List.foldr (\e rec -> do
                          r <- rec
                          e' <- translate_expression e label
                          return (e':r)) (return []) elist
  update_ref ref (\ri -> Just ri { r_expression = Left $ ETuple ref elist' })
  return (ETuple ref elist')

translate_expression (S.EIf e f g) label = do
  ref <- create_ref
  e' <- translate_expression e label
  f' <- translate_expression f label
  g' <- translate_expression g label
  update_ref ref (\ri -> Just ri { r_expression = Left $ EIf ref e' f' g' })
  return (EIf ref e' f' g')

translate_expression (S.EBox t) label = do
  ex <- get_location
  ref <- create_ref
  t' <- translate_bound_type t label
  -- Check that the type of the box is a quantum data type
  qdata <- Q.is_qdata_type t'
  if not qdata then do
    prt <- pprint_type_noref t'
    throwQ (BadBoxType prt) ex

  else do
    -- The translation of the type of the box in the core syntax produces
    -- some constraints that needs to be conveyed to the type inference
    -- Using a scheme is a way of doing it
    update_ref ref (\ri -> Just ri { r_expression = Left $ EBox ref t' })
    return (EBox ref t')

translate_expression S.EUnbox _ = do
  ref <- create_ref
  update_ref ref (\ri -> Just ri { r_expression = Left $ EUnbox ref })
  return (EUnbox ref)

translate_expression S.ERev _ = do
  ref <- create_ref
  update_ref ref (\ri -> Just ri { r_expression = Left $ ERev ref })
  return (ERev ref)

translate_expression (S.ELocated e ex) label = do
  set_location ex
  translate_expression e label

translate_expression (S.EBuiltin s) label = do
  ref <- create_ref
  -- Check the existence of the built-in value before translating it
  ctx <- get_context
  case Map.lookup s builtin_all of
    Just (typ, val) -> do
        -- Translate the type
        typ' <- translate_bound_type typ label
        set_context $ ctx { builtins = Map.insert s (typ',val) (builtins ctx) }
        update_ref ref (\ri -> Just ri { r_expression = Left $ EBuiltin ref s })
        return $ EBuiltin ref s

    Nothing -> do
        -- Wrong, no built-in of name s has been defined
        ex <- get_location
        throwQ (UndefinedBuiltin s) ex

translate_expression (S.EConstraint e t) label = do
  e' <- translate_expression e label
  return $ EConstraint e' (t, L.types label)



-- | If an interface file is provided, modify the pattern by adding type constraints corresponding to the types
-- written in the interface.
with_interface :: S.Program -> LabellingContext -> Pattern -> QpState Pattern
with_interface prog label (PVar ref x) = do
  case S.interface prog of
    Just inter -> do
        -- If an interface file is present, check the presence of the variable x
        n <- variable_name x
        case List.lookup n inter of
          Just typ -> do
              return $ PConstraint (PVar ref x) (typ, L.types label)
          Nothing -> do
              return $ PVar ref x
    Nothing -> do
        return $ PVar ref x

with_interface prog label (PDatacon ref dcon (Just p)) = do
  p' <- with_interface prog label  p
  return $ PDatacon ref dcon $ Just p'

with_interface prog label (PTuple ref plist) = do
  plist' <- List.foldr (\p rec -> do
                          r <- rec
                          p' <- with_interface prog label p
                          return (p':r)) (return []) plist
  return $ PTuple ref plist

with_interface prog label (PConstraint p t) = do
  p' <- with_interface prog label  p
  return (PConstraint p' t)

with_interface _ _ p =
  return p
