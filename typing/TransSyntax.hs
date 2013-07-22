module TransSyntax (define_user_subtyping,
                    translate_program,
                    translate_type,
                    translate_body,
                    import_typedefs,
                    update_module_types) where

import Utils
import Classes
import Localizing
import QuipperError

import CoreSyntax
import CorePrinter

import Syntax (RecFlag (..))
import qualified Syntax as S
import Printer

import TypeInference (unfold_user_constraint, break_composite)

import QpState
import Modules

import Gates

import Control.Exception

import Data.Map as Map
import qualified Data.List as List
import qualified Data.IntMap as IMap

-- | The typing constraints  {user a <: user a'} don't make much sense as is, so they need
-- to be converted to some constraints about the arguments, like {user a <: user a'} == {a <: a'}
-- This is done by unfolding the definition of the user type, and comparing the types of the data
-- constructors one on one :
--
-- with the type     either a b = Left of a | Right of b
-- we get   {either a b <: either a' b'} == { a <: a', b <: b' }
--
-- With inductive types, the method is the same, and the type is recursively unfolded, until the
-- constraint set becomes stable :
--
-- with the type     list a = Nil | Cons of a * list a
-- we get   {list a <: list a'} == {a * list a <: a' * list a'}
--                              == {a <: a', list a <: list a'}
--                              == ... == {a <: a'} removing the constraint {list a <: list a'}


-- | Unfold the definitions of the types in the subtyping constraints
-- products of the reduction of user a <: user a'
-- Takes the name of the type as input, and returns the resulting set.
-- No modification is made to the specification of the type.
unfold_once :: String -> QpState [TypeConstraint]
unfold_once name = do
  spec <- type_spec name
  
  -- Unfolded constraints
  (a, a', current) <- return $ subtype spec
  

  -- Isolate the user type constraints
  (cuser, cnuser) <- return $ List.partition is_user current

  -- unfold the user type constraints
  cuser <- List.foldl (\rec (Subtype (TBang n (TUser utyp arg)) (TBang m (TUser utyp' arg'))) -> do
                         r <- rec
                         cset <- unfold_user_constraint utyp arg utyp' arg'
                         return $ cset <> r) (return emptyset) cuser

  -- Break the composite constraints, although without touching
  -- the user type constraints, thus the false flag in the call to break_composite
  (cuser, _) <- break_composite False cuser

  -- Add them one by one to the non user constraints, checking
  -- for duplicates
  cnuser <- List.foldl (\rec c -> do
                          r <- rec
                          if List.elem c r then
                            return r
                          else
                            return (c:r)) (return cnuser) cuser

  return cnuser


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
                                 before <- return $ List.filter (not . is_user) subt
                                 (cuser, cnuser) <- return $ List.partition is_user after
                          
                                 -- Check the stability of the non user constraints of before and after the unfolding
                                 if cnuser List.\\ before == [] && before List.\\ cnuser == [] then do
                                   -- Terminate the recursion, and retain in the subtyping of n only the non user constraints
                                   newlog 0 ("[" ++ List.foldl (\rec c -> " " ++ pprint c ++ rec) "" before ++ " ] => " ++
                                             pprint (TUser n a) ++ " <: " ++ pprint (TUser n a'))

                                   return (b, ctx { types = Map.insert n (spec { subtype = (a, a', before) }) $ types ctx })
                                 else do
                                   -- Continue the recursion, but update the subtyping of n
                                   return (n:b, ctx { types = Map.insert n (spec { subtype = (a, a', after) }) $ types ctx })) (return ([], ctx)) (List.zip3 names specs unfolded) 

  -- Continue or not with the recursion
  set_context ctx
  unfold_all finish


-- | Define the subtyping relations for all the user defined types
-- It basically applies the unfold_all function, after having initialized the contraint sets based
-- on the unfolded definition of the user types
define_user_subtyping :: [S.Typedef] -> QpState () 
define_user_subtyping typedefs = do
  newlog 0 ">> Extension of the subtyping relation to user types"
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
                                              ufold' <- return $ List.map (subs_typ_var x $ TVar y) ufold'
                                              ufold' <- return $ List.map (subs_flag n m) ufold'
                                              return (b:a', ufold')) (return ([], ufold)) a

                -- Generate the constraints ufold <: ufold'
                constraints <- List.foldl (\rec (t, u) -> do
                                             r <- rec
                                             (lc, _) <- break_composite False ([t <: u], [])    -- We don't want the user type constraints to be replaced yet
                                             return $ lc ++ r) (return []) (List.zip ufold ufold')

                ctx <- get_context
                set_context $ ctx { types = Map.insert n (spec { subtype = (a, a', constraints) }) $ types ctx }) (return ()) names

  -- Unfold until the constraint set is stable
  unfold_all names
  newlog 0 "<<\n"


-- | Import the type definitions in the current state
-- The data constructors are labelled during this operation, and included in the field datacons of the state
-- User types are added the same, with an id set to -1 to distinguish them from other type variables
import_typedefs :: [S.Typedef] -> QpState (Map String Int)
import_typedefs typedefs = do
  -- Import the names of the types in the current labelling map
  -- This operation permits the writing of inductive types
  m <- List.foldl (\rec (S.Typedef typename args _) -> do
                     m <- rec
                     n <- fresh_flag
                     spec <- return $ Spec { args = List.length args, unfolded = ([], []), subtype = ([], [], []) }

                     -- Register the type in the current context
                     register_type typename spec

                     -- Add an entry to the current module
                     cm <- get_module
                     ctx <- get_context
                     set_context $ ctx { cmodule = cm { typespecs = Map.insert typename spec $ typespecs cm } }

                     return $ Map.insert typename (TBang n $ TUser typename []) m) (return Map.empty) typedefs

  -- Transcribe the rest of the type definitions
  -- Type definitions include : the name of the type, generic variables, the list of constructors
  List.foldl (\rec (S.Typedef typename args dlist) -> do
                lbl <- rec

                -- Bind the arguments of the type
                -- For each string argument a, a type !n a is created and bound
                (args', m') <- List.foldr (\a rec -> do
                                             (args, m) <- rec
                                             ta <- new_type
                                             return (ta:args, Map.insert a ta m)) (return ([], m)) args

                -- Define the type of the data constructors
                (dtypes', m) <- List.foldr (\(dcon, dtype) rec -> do
                                             (dt, lbl) <- rec
                                             (dtype', dtype'', cset) <- case dtype of
                                                                 -- If the constructor takes no argument
                                                                 Nothing -> do
                                                                     n <- fresh_flag 
                                                                     return (TBang n (TUser typename args'), TBang n TUnit, emptyset)

                                                                 -- If the constructor takes an argument
                                                                 Just dt -> do
                                                                     -- The same flag is used to mark the argument and the return value of the function
                                                                     (dt'@(TBang n _), cset) <- translate_type dt [] m'
                                                                     return (TBang anyflag (TArrow dt' (TBang n $ TUser typename args')), dt', cset)

                                             -- Generalize the type of the constructor over the free variables and flags
                                             -- Those variables must also respect the constraints from the construction of the type
                                             (fv, ff) <- return (free_typ_var dtype', free_flag dtype')
                                             dtype' <- return $ TForall fv ff cset dtype'

                                             -- Register the datacon
                                             id <- register_datacon dcon dtype'
                                             return $ (dtype'':dt, Map.insert dcon id lbl)) (return ([], lbl)) dlist

                -- Update the specification of the type
                spec <- type_spec typename
                ctx <- get_context
                set_context $ ctx { types = Map.insert typename (spec { unfolded = (args', dtypes') }) $ types ctx }
                return m) (return Map.empty) typedefs 


-- | Transfer the type definitions from the state monad to the current module
-- This function assumes that the current module already have entries corresponding to its types, and
-- then just updates them
update_module_types :: QpState ()
update_module_types = do
  cmod <- get_module
  cmod' <- Map.foldWithKey (\typename _ rec -> do
                              cm <- rec
                              spec <- type_spec typename
                              return $ cm { typespecs = Map.insert typename spec (typespecs cm) }) (return cmod) (typespecs cmod)
  ctx <- get_context
  set_context $ ctx { cmodule = cmod' }



-- | Translate a type, given a labelling.
-- The arguments of type applications are passed via the function calls
-- The output includes a set of structural constraints : eg !p (!n a * !m b) imposes p <= n and p <= m
translate_type :: S.Type -> [Type] -> Map String Type -> QpState (Type, ConstraintSet)
translate_type S.TUnit [] _ = do
  return (TBang anyflag TUnit, emptyset)

translate_type S.TBool [] _ = do
  return (TBang anyflag TBool, emptyset)

translate_type S.TQBit [] _ = do
  return (TBang zero TQbit, emptyset)

translate_type (S.TVar x) arg label = do
  case Map.lookup x label of
    -- This case corresponds to user types
    Just (TBang _ (TUser _ _)) -> do
        -- Expected number of args
        spec <- type_spec x
        nexp <- return $ args spec
        -- Actual number of args
        nact <- return $ List.length arg

        if nexp == nact then do
          n <- fresh_flag
          return (TBang n (TUser x arg), emptyset)
        else do
          ex <- get_location
          f <- get_file
          throw $ WrongTypeArguments x nexp nact (f, ex)

    Just typ ->
        if arg == [] then
          return (typ, emptyset)
        else do
          ex <- get_location
          f <- get_file
          throw $ WrongTypeArguments (pprint typ) 0 (List.length arg) (f, ex)

    Nothing -> do
        ex <- get_location
        f <- get_file
        throw $ UnboundVariable x (f, ex)

translate_type (S.TQualified m x) arg _ = do
  spec <- lookup_qualified_type (m, x)
  -- Expected number of args
  nexp <- return $ args spec
  -- Actual number of args
  nact <- return $ List.length arg

  if nexp == nact then do
    n <- fresh_flag
    return (TBang n (TUser x arg), emptyset)
  else do
    ex <- get_location
    f <- get_file
    throw $ WrongTypeArguments x nexp nact (f, ex)

translate_type (S.TArrow t u) [] label = do
  (t', csett) <- translate_type t [] label
  (u', csetu) <- translate_type u [] label
  n <- fresh_flag
  return (TBang n (TArrow t' u'), csett <> csetu)

translate_type (S.TTensor tlist) [] label = do
  n <- fresh_flag
  (tlist', cset') <- List.foldr (\t rec -> do
                                   (r, cs) <- rec
                                   (t'@(TBang m _), cs') <- translate_type t [] label
                                   return ((t':r), [(n, m)] <> cs' <> cs)) (return ([], emptyset)) tlist
  return (TBang n (TTensor tlist'), cset')

translate_type (S.TBang t) [] label = do
  (TBang _ t, cset) <- translate_type t [] label
  return (TBang 1 t, cset)

translate_type (S.TCirc t u) [] label = do
  (t', csett) <- translate_type t [] label
  (u', csetu) <- translate_type u [] label
  return (TBang anyflag (TCirc t' u'), csett <> csetu)

-- Case of type application : the argument is pushed onto the arg list
translate_type (S.TApp t u) args label = do
  (u', cset) <- translate_type u [] label
  (t', cset') <- translate_type t (u':args) label
  return (t', cset <> cset')

translate_type (S.TLocated t ex) args label = do
  set_location ex
  translate_type t args label

-- Remaining cases : of types applied to an argument when they are not generic
translate_type t args label = do
  ex <- get_location
  f <- get_file
  throw $ WrongTypeArguments (pprint t) 0 (List.length args) (f, ex)



-- | Translate a pattern, given a labelling
-- The map is updated, as the variables are bound in the pattern
translate_pattern_with_label :: S.Pattern -> Map String Int -> QpState (Pattern, Map String Int)
translate_pattern_with_label S.PUnit label = do
  return (PUnit, label)

translate_pattern_with_label (S.PVar x) label = do
  id <- register_var x
  return (PVar id, Map.insert x id label)

translate_pattern_with_label (S.PTuple plist) label = do
  (plist', lbl) <- List.foldr (\p rec -> do
                                  (r, lbl) <- rec
                                  (p', lbl') <- translate_pattern_with_label p lbl
                                  return ((p':r), lbl')) (return ([], label)) plist
  return (PTuple plist', lbl)

translate_pattern_with_label (S.PDatacon datacon p) label = do
  case Map.lookup datacon label of
    Just id -> do
        case p of
          Just p -> do
              (p', lbl) <- translate_pattern_with_label p label
              return (PDatacon id (Just p'), lbl)

          Nothing ->
              return (PDatacon id Nothing, label)

    Nothing -> do
        ex <- get_location
        f <- get_file
        throw $ UnboundDatacon datacon (f, ex)

translate_pattern_with_label (S.PLocated p ex) label = do
  set_location ex
  (p', lbl) <- translate_pattern_with_label p label
  return (PLocated p' ex, lbl)


-- | Translate an expression, given a labelling map
translate_expression_with_label :: S.Expr -> Map String Variable -> QpState Expr
translate_expression_with_label S.EUnit _ = do
  return EUnit

translate_expression_with_label (S.EBool b) _ = do
  return (EBool b)

translate_expression_with_label (S.EVar x) label = do
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
        throw $ UnboundVariable x (f, ex)

translate_expression_with_label (S.EQualified m x) _ = do
  id <- lookup_qualified_var (m, x)
  return $ EGlobal id

translate_expression_with_label (S.EFun p e) label = do
  (p', lbl) <- translate_pattern_with_label p label
  e' <- translate_expression_with_label e lbl
  return (EFun p' e')

translate_expression_with_label (S.ELet r p e f) label = do
  (p', lbl) <- translate_pattern_with_label p label
  case r of
    Recursive -> do
        e' <- translate_expression_with_label e lbl
        f' <- translate_expression_with_label f lbl
        return (ELet r p' e' f')

    Nonrecursive -> do
        e' <- translate_expression_with_label e label
        f' <- translate_expression_with_label f lbl
        return (ELet r p' e' f')

translate_expression_with_label (S.EDatacon datacon e) label = do
  case Map.lookup datacon label of
    Just id -> do
        case e of
          Just e -> do
              e' <- translate_expression_with_label e label
              return (EDatacon id $ Just e')

          Nothing ->
              return (EDatacon id Nothing)

    Nothing -> do
        ex <- get_location
        f <- get_file
        throw $ UnboundDatacon datacon (f, ex)

translate_expression_with_label (S.EMatch e blist) label = do
  e' <- translate_expression_with_label e label
  blist' <- List.foldr (\(p, f) rec -> do
                          r <- rec
                          (p', lbl) <- translate_pattern_with_label p label
                          f' <- translate_expression_with_label f lbl
                          return ((p', f'):r)) (return []) blist
  return (EMatch e' blist')

translate_expression_with_label (S.EApp e f) label = do
  e' <- translate_expression_with_label e label
  f' <- translate_expression_with_label f label
  return (EApp e' f')

translate_expression_with_label (S.ETuple elist) label = do
  elist' <- List.foldr (\e rec -> do
                          r <- rec
                          e' <- translate_expression_with_label e label
                          return (e':r)) (return []) elist
  return (ETuple elist')

translate_expression_with_label (S.EIf e f g) label = do
  e' <- translate_expression_with_label e label
  f' <- translate_expression_with_label f label
  g' <- translate_expression_with_label g label
  return (EIf e' f' g')

translate_expression_with_label (S.EBox t) _ = do
  -- Types
  ctx <- get_context
  typs <- return $ Map.mapWithKey (\typename _ -> TBang (-1) $ TUser typename []) (types ctx)

  (t', cset) <- translate_type t [] typs
  -- The translation of the type of the box in the core syntax produces
  -- some constraints that needs to be conveyed to the type inference
  -- Using a scheme is a way of doing it
  return (EBox (TForall [] [] cset t'))

translate_expression_with_label S.EUnbox _ = do
  return EUnbox

translate_expression_with_label S.ERev _ = do
  return ERev

translate_expression_with_label (S.ELocated e ex) label = do
  set_location ex
  e' <- translate_expression_with_label e label
  return $ ELocated e' ex


-- Label the gates
import_gates :: QpState (Map String Int)
import_gates = do
  li0 <- register_var "INIT0"
  li1 <- register_var "INIT1"
  ti0 <- register_var "TERM0"
  ti1 <- register_var "TERM1"

  m <- return $ Map.fromList [("INIT0", li0), ("INIT1", li1), ("TERM0", ti0), ("TERM1", ti1)]

  m' <- List.foldl (\rec g -> do
                      m <- rec
                      id <- register_var g
                      return $ Map.insert g id m) (return m) unary_gates
  
  List.foldl (\rec g -> do
                m <- rec
                id <- register_var g
                return $ Map.insert g id m) (return m') binary_gates


-- | Translate a whole program
-- Proceeds in three steps:
--   Import the type definitions
--   Import the gates
--   Translate the expression body
translate_program :: S.Program -> QpState Expr
translate_program prog = do
  dcons <- import_typedefs $ S.typedefs prog
  define_user_subtyping $ S.typedefs prog

  gates <- import_gates
  ctx <- get_context
  set_context $ ctx { gatesid = gates }

  translate_body (S.body prog) (Map.union dcons gates)


-- | Translate and merge the list of term declarations
translate_body :: [S.Declaration] -> Map String Int -> QpState Expr
-- The general type of a file, if empty, is unit
translate_body [] _ =
  return EUnit

-- However, if the last declaration is an expression,
-- it becomes the return value of the evaluation
translate_body [S.DExpr e] lbl = do
  translate_expression_with_label e lbl

-- If an lonely expression is encountered, it is ignored
translate_body ((S.DExpr _):rest) lbl = do
  translate_body rest lbl

-- If a variable declaration is encountered,
-- the variables of the pattern are marked to be exported,
-- and the "let p = e" is connected with the rest of the body
translate_body ((S.DLet recflag p e):rest) lbl = do
  (p', lbl') <- translate_pattern_with_label p lbl
  -- Export the variables of the pattern
  List.foldl (\rec x -> do
                rec
                export_var x) (return ()) (free_var p')
  -- Connect the let
  e' <- translate_expression_with_label e (if recflag == Recursive then lbl' else lbl)
  r <- translate_body rest lbl'
  return (ELet recflag p' e' r)


