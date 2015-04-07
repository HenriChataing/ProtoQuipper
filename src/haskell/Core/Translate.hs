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
  TranslateState (..),
  Core.Translate.init,
  translateType,
  translateBoundType,
  translateUnboundType,
  translateExpression,
  translatePattern,
  translateDeclaration,
  translateDeclarations,
  importAlgebraic,
  importSynonym) where

import Utils
import Classes
import Builtins

import Core.Syntax
import Core.Environment as Environment hiding (types)
import qualified Core.Environment as Environment (types)
import Core.Printer

import Language.Type as Type
import Language.Constructor as Constructor

import qualified Parsing.Syntax as S
import Parsing.Location hiding (location)
import Parsing.Printer

import Interpreter.Circuits as C

import Compiler.SimplSyntax (tagAccessor)
import qualified Compiler.SimplSyntax as CS

import Monad.Error
import Monad.Core as Core hiding (environment)
import qualified Monad.Core as Core (environment)

import Data.Map as Map
import qualified Data.List as List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet

import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Monad.Trans.Reader


-- ------------------------------------------------------------------------------------------------
-- * Translation context.

-- Contains the local namespace along with some options.
data TranslateState = TranslateState {
  bound :: Bool,                -- ^ Raise errors if unbound types are found.
  location :: Extent,           -- ^ Current file location.
  environment :: Environment,   -- ^ Toplevel environment.
  types :: Map String Type,         -- ^ Local type context.
  currentModule :: String           -- ^ Current module.
}

-- | Monad of the translation algorithm.
type Translate = StateT TranslateState Core


-- | Build the initial translate state.
init :: String -> [String] -> Core TranslateState
init moduleName dependencies = do
  let state = TranslateState {
        bound = False,
        location = unknownExtent,
        types = Map.empty,
        environment = Environment.empty,
        currentModule = moduleName
      }
  List.foldl (\rec dep -> do
      state <- rec
      pack <- require dep
      let typs = Map.map (\id ->
            TypeAnnot 0 $ TypeApply (TypeUser id) []
            ) $ Environment.types $ Core.environment pack
      return state {
          environment = (environment state) <+> (Core.environment pack),
          types = Map.union (types state) typs
        }
    ) (return state) dependencies


-- | Return term informaton (with a dummy type).
getInfo :: Translate Info
getInfo = do
  ext <- gets location
  return $ Info ext unit

-- | Perform a piece of computation before restoring the types to its previous state.
localType :: Translate a -> Translate a
localType comp = do
  types <- gets types
  r <- comp
  modify $ \state -> state { types = types }
  return r

-- | Perform a piece of computation before restoring the variablemap to its previous state.
localVar :: Translate a -> Translate a
localVar comp = do
  variables <- gets (Environment.variables . environment)
  r <- comp
  modify $ \state ->
      state { environment = (environment state) { Environment.variables = variables } }
  return r


-- | Look up a variable in a specific module (typically used with a qualified variable). The input
-- pair is (Module, Var).
lookupQualified :: String -> String -> (Module -> Map String a) -> Translate a
lookupQualified modname n inside = do
  mod <- lift $ Core.require modname
  -- Check that the module is part of the dependencies.
  case Map.lookup n $ inside mod of
    Just x -> return x
    Nothing -> throwUnboundVariable n


-- | Generic error for unbound values (variables, data constructors, types, builtins).
throwUnboundValue :: QError a => String -> (String -> a) -> Translate b
throwUnboundValue v err = do
  ext <- gets location
  throwNE (err v) ext

-- | Throw an unbound module error.
throwUnboundModule :: String -> Translate a
throwUnboundModule mod =
  throwUnboundValue mod UnboundModule


-- | Throw an unbound variable error.
throwUnboundVariable :: String -> Translate a
throwUnboundVariable n =
  throwUnboundValue n UnboundVariable


-- | Throw an unbound data constructor error.
throwUnboundDatacon :: String -> Translate a
throwUnboundDatacon n =
  throwUnboundValue n UnboundDatacon


-- | Throw an undefined type error.
throwUndefinedType :: String -> Translate a
throwUndefinedType n =
  throwUnboundValue n UndefinedType


-- | Throw an undefined builtin error.
throwUndefinedBuiltin :: String -> Translate a
throwUndefinedBuiltin n =
  throwUnboundValue n UndefinedBuiltin


-- ------------------------------------------------------------------------------------------------
-- * Type definitions.

-- | From a given type written in the parsing syntax, produce a map that associates each free
-- variable with its variance.
variance :: Variance                        -- ^ The variance of the current type.
         -> S.Type                          -- ^ The type to check.
         -> [S.Type]                        -- ^ The type arguments.
         -> Map String Type                 -- ^ A partial labelling context.
         -> Core (Map String Variance)      -- ^ The resulting map.
-- The variance of a variance is the global variance.
variance var (S.TVar a) [] typs = return $ Map.singleton a var
variance var (S.TVar a) args typs = do
  -- The variance of each of the type arguments depends upon the variance imposed by the type.
  vars <- case Map.lookup a typs of
      Just (TypeAnnot _ (TypeApply (TypeUser typ) [])) -> do
        def <- getTypeDefinition typ
        return $ List.map snd $ arguments def
      _ -> fail "Translate:variance: undefined type"
  -- Infer the variance for all type arguments.
  List.foldl (\rec (vara, a) -> do
      map <- rec
      let var' = case vara of
            Unrelated -> Unrelated
            Equal -> Equal
            Covariant -> var
            Contravariant -> opposite var
      vara <- variance var' a [] typs
      return $ Map.unionWith join vara map
    ) (return Map.empty) $ List.zip vars args
-- The tensor is covariant for all arguments.
variance var (S.TTensor tensor) [] typs =
  List.foldl (\rec a -> do
      map <- rec
      vara <- variance var a [] typs
      return $ Map.unionWith join vara map
    ) (return Map.empty) tensor
-- Idem, the variance is unchanged.
variance var (S.TBang t) [] typs = variance var t [] typs
-- Just flatten the application.
variance var (S.TApp t u) arg typs = variance var t (u:arg) typs
-- Ignore the extent.
variance var (S.TLocated t _) arg typs = variance var t arg typs
-- Contravariant in the domain, covariant in the codomain.
-- This applies to circ and arrow types.
variance var (S.TCirc t u) [] typs = do
  vt <- variance (opposite var) t [] typs
  vu <- variance var u [] typs
  return $ Map.unionWith join vt vu
variance var (S.TArrow t u) [] typs = do
  vt <- variance (opposite var) t [] typs
  vu <- variance var u [] typs
  return $ Map.unionWith join vt vu
-- Other types, with no type variables.
variance _ _ _ _ = return Map.empty


-- | Import a block of mutually recursive algebraic type definitions in the current state. The data
-- constructors are labelled during this operation, their associated type translated, and themselves
-- included in the field datacons of the state.
importAlgebraic :: [S.TypeAlgebraic]              -- ^ A block of co-inductive type definitions.
                -> Translate ()
importAlgebraic block = do
  -- Create the type definitions (empty initially), and import the type constructors in the context.
  block' <- List.foldl (\rec def @ (S.Typedef typename args _) -> do
      block <- rec
      let arguments = List.map (\a -> (unit, Unrelated)) args
      mod <- gets currentModule
      let def' = TypeInfo typename mod (Algebraic False arguments []) tagAccessor
      -- Register the type in the current context.
      id <- lift $ registerTypeDefinition def'
      -- Add the type to the labelling context.
      let typ = TypeAnnot 0 $ TypeApply (TypeUser id) []
      modify $ \state -> state { types = Map.insert typename typ $ types state }
      return $ (id, def, Algebraic False arguments []):block
    ) (return []) block

  -- Build the unfolded type definition.
  List.foldl (\rec (S.Typedef typename args constructors) -> do
      rec
      -- Type id needed for updates.
      types <- gets types
      typid <- case Map.lookup typename types of
          Just (TypeAnnot _ (TypeApply (TypeUser id) _)) -> return id
          _ -> fail "TransSyntax:importAlgebraic: unexpected non-algebraic type"
      -- Bind the arguments of the type. For each string argument a, a type !n a is created and bound
      -- locally in the monad state.
      (args, types') <- List.foldr (\x rec -> do
          (args, map) <- rec
          a <- lift newType
          return (a:args, Map.insert x a map)
        ) (return ([], types)) args
      modify $ \state -> state { types = types' }

      -- Translate the type of the data constructors.
      (_, dtypes) <- List.foldl (\rec (cons, argtyp) -> do
          (tag, dtyps) <- rec
          m <- lift freshFlag
          (ctyp, argtyp, cset) <- case argtyp of
              -- If the constructor takes no argument.
              Nothing -> return (TypeAnnot m $ TypeApply (TypeUser typid) args, Nothing, emptyset)
              -- If the constructor takes one argument.
              Just atyp -> do
                atyp @ (TypeAnnot n _) <- translateBoundType atyp
                return (
                      arrow atyp $ TypeAnnot m $ TypeApply (TypeUser typid) args,
                      Just atyp,
                      ConstraintSet [] [Le m n noInfo])
          -- Generalize the type of the constructor over the free variables and flags. Those variables
          -- must also respect the constraints from the construction of the type.
          let ctyp' = TypeScheme (IntSet.toList $ freeflag ctyp) (IntSet.toList $ freevar ctyp) cset ctyp
          -- Register the datacon.
          id <- lift $ registerConstructor $ Constructor.init cons "" typid ctyp' tag
          modify $ \state ->
              let constrs = Environment.constructors $ environment state in
              state {
                  environment = (environment state) {
                      Environment.constructors = Map.insert cons id constrs }
                    }
          return (tag+1, (id, argtyp):dtyps)
        ) (return (0, [])) constructors
      -- Update the specification of the type.
      lift $ changeTypeDefinition typid $ \info ->
        case definition info of
          Algebraic dup vars _ ->
            let args' = List.map (\((_, v), a) -> (a, v)) $ List.zip vars args in
            info { definition = Algebraic dup args' dtypes }
          _ -> info
      -- Reset the type map (effectively remove the type variables).
      modify $ \state -> state { types = types }
    ) (return ()) block

  -- Update the variance of the type arguments of a single type.
  let updateVariance (typid, def, def') = do
        let (args, old) = List.unzip $ arguments def'
        let dotest = List.map (\(_, t) ->
              case t of { Nothing -> S.TUnit ; Just t -> t }) $ S.definition def
        types <- gets types
        varmap <- lift $ variance Covariant (S.TTensor dotest) [] types
        let new = List.map (\a ->
              case Map.lookup a varmap of { Nothing -> Unrelated ; Just var -> var }) $ S.arguments def
            newargs = List.zip args new
        lift $ changeTypeDefinition typid $ \info ->
          case definition info of
            Algebraic dup _ constrs -> info { definition = Algebraic dup newargs constrs }
            _ -> info
        return (old == new, (typid, def, def' { arguments = newargs }))

  -- Apply the function updateVariance to a group of type definitions.
  let updateVariances block = do
        (end, block) <- List.foldl (\rec typ -> do
            (end, block) <- rec
            (upd, typ') <- updateVariance typ
            return (end && upd, typ':block)
          ) (return (True, [])) block
        if end then return block
        else updateVariances block

  -- Print the information relevant to a type (constructors, ...).
  let printInfo (typid, def, def') = do
        lift $ Core.log 0 $ List.foldl (\s ((_, var), a) ->
            s ++ " " ++ show var ++ a
          ) ("alg: " ++ S.name def) $ List.zip (arguments def') (S.arguments def)

  -- Compilation specifics.
  List.foldl (\rec (typid, _, _) -> do
      rec
      lift $ setTypeImplementation typid
    ) (return ()) block'
  -- Apply the function updateVariances.
  block' <- updateVariances block'
  -- Print some information about the inferred variance.
  List.foldl (\rec typ -> rec >> printInfo typ) (return ()) block'
  return ()


-- | Import a single type alias definition.
importSynonym :: S.TypeAlias          -- ^ A type synonym.
              -> Translate ()         -- ^ The updated labelling context.
importSynonym synonym = do
  -- Save the types.
  types <- gets types
  -- Bind the arguments to core types.
  let args = S.arguments synonym
  args' <- lift $ newTypes $ List.length args
  let map = List.foldl (\map (a, a') -> Map.insert a a' map) types $ List.zip args args'
  modify $ \state -> state { types = map }
  -- Translate the synonym type.
  alias <- translateBoundType (S.definition synonym)
  -- Determine the variance of each argument.
  types' <- gets Core.Translate.types
  varmap <- lift $ variance Covariant (S.definition synonym) [] types'
  let vars = List.map (\a ->
          case Map.lookup a varmap of
            Nothing -> Unrelated
            Just v -> v
        ) args
  -- Print it.
  lift $ Core.log 0 $ List.foldl (\s (var, a) ->
      s ++ " " ++ show var ++ a
    ) ("syn: " ++ S.name synonym) $ List.zip vars args
  -- Build and save the type definition.
  let arguments = List.zip args' vars
  mod <- gets currentModule
  let def' = TypeInfo (S.name synonym) mod (Synonym arguments False alias) tagAccessor
  typid <- lift $ registerTypeDefinition def'
  -- Reset the types and insert the new type alias.
  let typ = TypeAnnot 0 $ TypeApply (TypeUser typid) []
  modify $ \state -> state { types = Map.insert (S.name synonym) typ types }


-- ------------------------------------------------------------------------------------------------
-- * Translation of types.

-- | Translate a type, given a labelling. The type context is passed around in the dedicated
-- monad Translate.
translateType :: S.Type
              -> [Type]              -- ^ List of type arguments.
              -> Translate Type      -- ^ Translated type.
-- Builtin types.
translateType S.TUnit [] = return unit
translateType S.TBool [] = return bool
translateType S.TInt [] = return int
translateType S.TQubit [] = return qubit

translateType (S.TLocated t ext) args = do
  modify $ \state -> state { location = ext }
  translateType t args

translateType (S.TCirc t u) [] = do
  t' <- translateType t []
  u' <- translateType u []
  return $ circ t' u'

translateType (S.TArrow t u) [] = do
  t' <- translateType t []
  u' <- translateType u []
  n <- lift freshFlag
  return $ apply n "->" [t', u']

translateType (S.TTensor ts) [] = do
  n <- lift freshFlag
  ts' <- List.foldl (\rec t -> do
      ts <- rec
      t' <- translateType t []
      return $ t':ts) (return []) ts
  return $ apply n "*" $ List.reverse ts'

-- Case of type application: the argument is pushed onto the arg list.
translateType (S.TApp t u) args = do
  u' <- translateType u []
  translateType t (u':args)

-- Bang type. The annotation associated with t is just ignored.
translateType (S.TBang t) [] = do
  TypeAnnot _ t' <- translateType t []
  return $ TypeAnnot 1 t'

-- The context is updated locally only.
translateType (S.TScheme a typ) [] = do
  a' <- lift newType
  localType $ do
    modify $ \state -> state { types = Map.insert a a' $ types state }
    translateType typ []

translateType (S.TVar x) args = do
  types <- gets types
  case Map.lookup x types of

    -- The variable is an algebraic / synonym type.
    Just (TypeAnnot _ (TypeApply (TypeUser id) args')) -> do
      def <- lift $ getTypeDefinition id
      -- Check the number of arguments against the expected number.
      -- Could be refined by doing an overall kind analysis.
      let expected = List.length $ arguments def
          actual = List.length args' + List.length args
      if expected == actual then do
        n <- lift freshFlag
        return $ TypeAnnot n $ TypeApply (TypeUser id) (args' ++ args)
      else do
        ext <- gets location
        throwNE (WrongTypeArguments x expected actual) ext

    -- The variable is just a bound type.
    Just typ ->
      if args == [] then return typ
      else do
        ext <- gets location
        throwNE (WrongTypeArguments (pprint typ) 0 (List.length args)) ext

    -- If the variable is not found, it can be a free variable (depending on the bound option).
    Nothing -> do
      bound <- gets bound
      -- If the type variables are supposed to be bound, this one isn't.
      if bound then do
        ext <- gets location
        throwNE (UnboundVariable x) ext
      -- Last case, if the type authorize free variables, register this one with a new type.
      else do
        t <- lift newType
        modify $ \state -> state { types = Map.insert x t types }
        return t

translateType (S.TQualified m x) args = do
  -- Expected number of arguments.
  typid <- lookupQualified m x (Environment.types . Core.environment)
  def <- lift $ getTypeDefinition typid
  let expected = List.length $ Type.arguments def
  -- Actual number.
  let actual = List.length args
  -- Compare.
  if expected == actual then do
    n <- lift freshFlag
    return $ TypeAnnot n $ TypeApply (TypeUser typid) args
  else do
    ext <- gets location
    throwNE (WrongTypeArguments x expected actual) ext

-- Remaining cases: of types applied to an argument when they are not generic.
translateType t args = do
  ext <- gets location
  throwNE (WrongTypeArguments (pprint t) 0 (List.length args)) ext


-- | Apply the function 'Typer.TransSyntax.translateType' to a bound type. The arguments must be
-- null initially.
translateBoundType :: S.Type -> Translate Type
translateBoundType t = do
  -- Set option in monad's state.
  modify $ \state -> state { bound = True }
  translateType t []


-- | Apply the function 'Typer.TransSyntax.translateType' to unbound types. The binding map is
-- initially empty, and is dropped after the translation of the type. No argument is passed to the
-- top type.
translateUnboundType :: S.Type -> Translate Type
translateUnboundType t = do
  -- Set option in monad's state.
  modify $ \state -> state { bound = False }
  translateType t []


-- | Translate a pattern, given a labelling map.
-- The map is updated as variables are bound in the pattern.
translatePattern :: S.XExpr -> Translate Pattern
translatePattern S.EUnit = do
  info <- getInfo
  return $ PConstant info ConstUnit

translatePattern (S.EBool b) = do
  info <- getInfo
  return $ PConstant info $ ConstBool b

translatePattern (S.EInt n) = do
  info <- getInfo
  return $ PConstant info $ ConstInt n

translatePattern S.EWildcard = do
  info <- getInfo
  return $ PWildcard info

translatePattern (S.EVar x) = do
  info <- getInfo
  mod <- gets currentModule
  id <- lift $ registerVariable (Just mod) x
  modify $ \state ->
      let variables = Environment.variables $ environment state in
      state { environment = (environment state) { variables = Map.insert x (Local id) variables } }
  return $ PVar info id

translatePattern (S.ETuple tuple) = do
  info <- getInfo
  tuple' <- List.foldl (\rec p -> do
      tuple <- rec
      p' <- translatePattern p
      return $ p':tuple) (return []) tuple
  return $ PTuple info $ List.reverse tuple'

translatePattern (S.EDatacon cons p) = do
  info <- getInfo
  constructors <- gets (Environment.constructors . environment)
  case Map.lookup cons constructors of
    Just id -> do
      case p of
        Just p -> do
          p' <- translatePattern p
          return $ PDatacon info id $ Just p'
        Nothing -> return $ PDatacon info id Nothing
    Nothing -> throwUnboundDatacon cons

translatePattern (S.ELocated p ext) = do
  modify $ \state -> state { location = ext }
  translatePattern p

translatePattern (S.ECoerce p t) = do
  p' <- translatePattern p
  types <- gets types
  return $ PCoerce p' t types

translatePattern (S.EApp (S.ELocated (S.EDatacon e Nothing) ex) f) =
  translatePattern (S.ELocated (S.EDatacon e $ Just f) ex)

translatePattern p = do
  ext <- gets location
  throwNE (ParsingError (pprint p)) ext


-- | Translate an expression in a local context given by the translation monad.
translateExpression :: S.XExpr -> Translate Expr
translateExpression S.EUnit = do
  info <- getInfo
  return $ EConstant info ConstUnit

translateExpression (S.EBool b) = do
  info <- getInfo
  return $ EConstant info $ ConstBool b

translateExpression (S.EInt n) = do
  info <- getInfo
  return $ EConstant info $ ConstInt n

translateExpression S.EUnbox = do
  info <- getInfo
  return $ EUnbox info

translateExpression S.ERev = do
  info <- getInfo
  return $ ERev info

translateExpression (S.ELocated e ext) = do
  modify $ \state -> state { location = ext }
  translateExpression e

translateExpression (S.ECoerce e t) = do
  e' <- translateExpression e
  types <- gets types
  return $ ECoerce e' (t, types)

translateExpression (S.EError msg) =
  return $ EError msg

translateExpression (S.EVar x) = do
  info <- getInfo
  variables <- gets (Environment.variables . environment)
  case Map.lookup x variables of
    Just (Local v) -> return $ EVar info v
    Just (Global v) -> return $ EGlobal info v
    Nothing -> throwUnboundVariable x

translateExpression (S.EQualified m x) = do
  info <- getInfo
  id <- lookupQualified m x (Environment.variables . Core.environment)
  case id of
    Local id -> return $ EGlobal info id
    Global id -> return $ EGlobal info id

translateExpression (S.EFun arg body) = do
  info <- getInfo
  localVar $ do
    arg' <- translatePattern arg
    body' <- translateExpression body
    return $ EFun info arg' body'

translateExpression (S.ELet r binder value body) = do
  -- At his point, p may be an applicative pattern,
  -- The arguments should be passed to the expression e.
  localVar $ do
    (binder', value') <- case r of
        Recursive -> do
          binder' <- translatePattern binder
          value' <- translateExpression value
          return (binder', value')
        Nonrecursive -> do
          value' <- translateExpression value
          binder' <- translatePattern binder
          return (binder', value')
    body' <- translateExpression body
    return $ ELet r binder' value' body'

translateExpression (S.EDatacon cons e) = do
  info <- getInfo
  constructors <- gets (Environment.constructors . environment)
  case Map.lookup cons constructors of
    Just id ->
      case e of
        Just e -> do
          e' <- translateExpression e
          return $ EDatacon info id $ Just e'
        Nothing ->  return $ EDatacon info id Nothing
    Nothing -> throwUnboundDatacon cons

translateExpression (S.EMatch e cases) = do
  info <- getInfo
  e' <- translateExpression e
  cases' <- List.foldl (\rec (p, f) -> do
      cases <- rec
      localVar $ do
        p' <- translatePattern p
        f' <- translateExpression f
        return $ (Binding p' f'):cases) (return []) cases
  return $ EMatch info e' $ List.reverse cases'

translateExpression (S.EApp e f) = do
  info <- getInfo
  e' <- translateExpression e
  f' <- translateExpression f
  -- Intercept constructor applications.
  case e' of
    EDatacon i cons Nothing -> return $ EDatacon info cons $ Just f'
    _ -> return $ EApp e' f'

translateExpression (S.ETuple tuple) = do
  info <- getInfo
  tuple' <- List.foldl (\rec e -> do
      tuple <- rec
      e' <- translateExpression e
      return $ e':tuple) (return []) tuple
  return $ ETuple info $ List.reverse tuple'

translateExpression (S.EIf e f g) = do
  e' <- translateExpression e
  f' <- translateExpression f
  g' <- translateExpression g
  return $ EIf e' f' g'

translateExpression (S.EBox t) = do
  info <- getInfo
  t' <- translateBoundType t
  return (EBox info t')

translateExpression e = do
  ext <- gets location
  throwNE (ParsingError (pprint e)) ext


-- | Translate a toplevel declaration into the core syntax.
translateDeclaration :: S.Declaration -> Translate (Maybe Declaration)
translateDeclaration (S.DLet loc rec binder value) = do
  -- We do not want to run this in a local environment, since the variables declared in the binder
  -- must be accessible for the next bindings.
  (binder', value') <- case rec of
      Recursive -> do
        binder' <- translatePattern binder
        value' <- translateExpression value
        return (binder', value')
      Nonrecursive -> do
        value' <- translateExpression value
        binder' <- translatePattern binder
        return (binder', value')
  return $ Just $ DLet noTermInfo { extent = loc } rec (extractVar binder') value'
  where
    extractVar (PVar _ x) = x
    extractVar _ = throwNE $ ProgramError "Translate:translateDeclaration: illegal pattern"

translateDeclaration (S.DExpr loc value) = do
  value' <- translateExpression value
  return $ Just $ DExpr noTermInfo { extent = loc } value'
translateDeclaration (S.DTypes block) = do
  importAlgebraic block
  return Nothing
translateDeclaration (S.DSyn alias) = do
  importSynonym alias
  return Nothing


-- | Translate all the toplevel declarations of a module.
translateDeclarations :: [S.Declaration] -> Translate [Declaration]
translateDeclarations declarations = do
  ds <- List.foldl (\rec d -> do
      ds <- rec
      d' <- translateDeclaration d
      case d' of
        Just d' -> return $ d':ds
        Nothing -> return ds
    ) (return []) declarations
  return $ List.reverse ds
