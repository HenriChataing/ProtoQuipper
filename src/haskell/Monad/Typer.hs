-- | ProtoQuipper uses a stack of reader monads in order to alleviate the complexity of a unique
-- state moned. The typer monad supports the generation of type and flag variables, and contains
-- the type substitution solution of the type constraints.

module Monad.Typer where

import Utils
import Classes
import Options (Options)
import Parsing.Location

import Core.Syntax -- (Type, LinearType, Flag, ConstraintInfo (..), ConstraintSource (..))

import Monad.Core as Core hiding (sourceType, typemap)
import qualified Monad.Core as Core (typemap)
import Monad.Error

import Control.Monad.Trans
import Control.Monad.Trans.State

import Data.IntMap as IntMap
import Data.IntSet as IntSet
import Data.List as List


-- | A list of assertions on types, that allows for control over the form of a type used in a
-- construction.
data Assertion =
    IsDuplicable
  | IsNonduplicable
  | IsNotfun
  deriving (Show, Eq)


-- | The type of values a flag can take. Initially, all flags are set to 'Unknown', except for some
-- that are imposed to 'Zero' or 'One' by the typing rules.
data FlagValue =
    Unknown   -- ^ The value of the flag has not been decided yet.
  | One       -- ^ The value 1.
  | Zero      -- ^ The value 0.
  deriving Show


-- | Information relevant to a flag. This contains the flag value. Eventually, it will also contain
-- various things such as reversibility, control, etc.
data FlagInfo = FlagInfo {
  flagValue :: FlagValue      -- ^ The value of the flag.
}


-- | The typer state is able to generate fresh type and flag variables, and define the substitution
-- solution of the type constraints.
data TyperState = TyperState {
  -- | Maps global variables to their respective type scheme.
  typemap :: IntMap TypeScheme,
  -- | The result of the unification: a mapping from type variables to linear types.
  mapping :: IntMap LinearType,
  -- | Flags from types are references to this map, which holds information about the value of the
  -- flag, but also about the type itself, for example the expression it is the type of. Such
  -- information is useful to send unambiguous error messages when the type inference fails.
  flags :: IntMap FlagInfo,
  -- | Type assertions.
  assertions :: [(Assertion, Type, Extent)]
}

-- | The typer monad, runs in the core monad.
type Typer = StateT TyperState Core


-- | Modify the options for the time of a monad computation.
withOptions :: (Options -> Options) -> Typer a -> Typer a
withOptions change computation = do
  options <- runCore getOptions
  runCore $ changeOptions change
  r <- computation
  runCore $ changeOptions (\_ -> options)
  return r


-- | Empty state.
init :: [String] -> Core TyperState
init depends = do
  let typer = TyperState {
        typemap = IntMap.empty,
        mapping = IntMap.empty,
        flags = IntMap.empty,
        assertions = []
        }
  List.foldl (\rec dep -> do
      typer <- rec
      mod <- require dep
      return typer {
          typemap = IntMap.union (typemap typer) $ Core.typemap mod
        }
    ) (return typer) depends

-- | Load the typemaps of the given dependencies.
load :: [String] -> Typer ()
load depends = do
  typemap <- List.foldl (\rec dep -> do
      typemap <- rec
      mod <- runCore $ require dep
      return $ IntMap.union typemap $ Core.typemap mod
    ) (return IntMap.empty) depends
  modify $ \typer -> typer { typemap = typemap }

---------------------------------------------------------------------------------------------------
-- * Assertions.

assert :: Assertion -> Type -> Extent -> Typer ()
assert what typ location =
  modify $ \typer -> typer { assertions = (what, typ, location):(assertions typer) }


-- | Check the assertions inserted via 'assert', and raise assert errors on fail. Checked assertions
-- are removed from the context.
checkAssertions :: Typer ()
checkAssertions = do
  asserts <- gets assertions
  -- Successively check all assertions.
  List.foldl (\rec (assert, typ, loc) -> do
      rec
      typ' <- resolveType typ
      case assert of
        IsDuplicable -> return ()
        IsNonduplicable -> return ()
        IsNotfun ->
          if not $ isFunction typ' then return ()
          else fail "Typer:checkAssertions: matched value has a function type"
    ) (return ()) asserts
  modify $ \typer -> typer { assertions = [] }


---------------------------------------------------------------------------------------------------
-- * Type map.

-- | Insert a new mapping /x/ |-> /t/ in the substitution, where /x/ is a type variable and /t/ is a
-- linear type.
mapsto :: Variable -> LinearType -> Typer ()
mapsto x t =
  modify $ \typer -> typer { mapping = IntMap.insert x t $ mapping typer }


-- | Look for a mapping of the argument variable. If no binding exists, the variable is returned unchanged.
resolveVar :: Variable -> Typer LinearType
resolveVar x = do
  mapping <- gets mapping
  case IntMap.lookup x mapping of
    Just t -> return t
    Nothing -> return $ TypeVar x


-- | Recursively apply the mappings recorded in the current state to a linear type.
resolveLinearType :: LinearType -> Typer LinearType
resolveLinearType (TypeVar x) = do
  t <- resolveVar x
  case t of
    -- If the value of x has been changed, reapply the mapping function, else returns the original type.
    TypeVar y | y /= x -> resolveLinearType $ TypeVar y
              | otherwise -> return $ TypeVar x
    t -> resolveLinearType t

resolveLinearType (TypeApply c args) = do
  args' <- List.foldl (\rec t -> do
      args <- rec
      t' <- resolveType t
      return $ t':args
    ) (return []) args
  return $ TypeApply c $ List.reverse args'


-- | Recursively apply the mappings recorded in the current state to a type. Qubits are intercepted
-- to check the value of their flag.
resolveType :: Type -> Typer Type
resolveType (TypeAnnot f t) = do
  t' <- resolveLinearType t
  case t' of
    TypeApply (TypeBuiltin "qubit") _ -> unsetFlag f noInfo
    _ -> return ()
  return $ TypeAnnot f t'


-- | Recursively apply the mappings recorded in the current state to a type scheme.  Qubits are
-- intercepted to check the value of their flag.
resolveScheme :: TypeScheme -> Typer TypeScheme
resolveScheme (TypeScheme fv ff cset typ) = do
  typ' <- resolveType typ
  return $ TypeScheme fv ff cset typ'


---------------------------------------------------------------------------------------------------
-- * Flags.

-- | Just update the information associated with a flag.
setFlagInfo :: Flag -> FlagInfo -> Typer ()
setFlagInfo flag info =
  modify $ \typer -> typer { flags = IntMap.insert flag info $ flags typer }

-- | Return the information associated with a flag.
getFlagInfo :: Flag -> Typer (Maybe FlagInfo)
getFlagInfo flag = do
  flags <- gets flags
  return $ IntMap.lookup flag flags

-- | Return the value of a flag.
getFlagValue :: Flag -> Typer FlagValue
getFlagValue f =
  case f of
    0 -> return Zero
    1 -> return One
    _ -> do
      info <- getFlagInfo f
      case info of
        Just (FlagInfo v) -> return v
        Nothing -> return Unknown


-- | Set the value of a flag to one. If the previously recorded value is incompatible with the new
-- one, generate an error (i.e.., old val = Zero).
setFlag :: Flag -> ConstraintInfo -> Typer ()
setFlag 0 info = throwNonDuplicableError info
setFlag 1 _ = return ()
setFlag flag info = do
  flags <- gets flags
  case IntMap.lookup flag flags of
    Just finfo ->
      case flagValue finfo of
        -- Cannot set the flag to 1, raise a typing error.
        Zero ->
          case sourceType info of
            Just typ -> do
              let typ0 = subs flag (0 :: Variable) typ
                  typ1 = subs flag (1 :: Variable) typ
              throwTypingError typ0 typ1 info { actual = True }
            Nothing -> throwNonDuplicableError info
        -- Update the flags.
        Unknown -> setFlagInfo flag finfo { flagValue = One }
        _ -> return ()

    Nothing -> setFlagInfo flag $ FlagInfo One

-- | Set the value of a flag to zero. If the previously recorded value is incompatible with the new
-- one, generate an error (i.e., old val = One).
unsetFlag :: Flag -> ConstraintInfo -> Typer ()
unsetFlag 1 info = throwNonDuplicableError info
unsetFlag 0 _ = return ()
unsetFlag flag info = do
  flags <- gets flags
  case IntMap.lookup flag flags of
    Just finfo -> do
      case flagValue finfo of
        -- Cannot set the flag to 0, raise a typing error.
        One ->
          case sourceType info of
            Just typ -> do
              let typ0 = subs flag (0 :: Variable) typ
                  typ1 = subs flag (1 :: Variable) typ
              throwTypingError typ0 typ1 info { actual = False, sourceType = Nothing }
            Nothing -> throwNonDuplicableError info
        -- Update the flags.
        Unknown -> setFlagInfo flag finfo { flagValue = Zero }
        _ -> return ()

    Nothing -> setFlagInfo flag $ FlagInfo Zero


-- | Create a new flag reference, initialized with the information of the argument flag.
duplicateFlag :: Flag -> Typer Flag
duplicateFlag ref = do
  case ref of
    0 -> return 0
    1 -> return 1
    _ -> do
      info <- getFlagInfo ref
      newref <- runCore freshFlag
      case info of
        Just i -> setFlagInfo newref i
        Nothing -> return ()
      return newref


---------------------------------------------------------------------------------------------------
-- * Type map.

-- | Return the type of a global variable (or fails if not found).
typeOf :: Variable -> Typer TypeScheme
typeOf x = do
  typemap <- gets typemap
  case IntMap.lookup x typemap of
    Just scheme -> return scheme
    Nothing -> do
      name <- runCore $ variableName x
      fail $ "Typer:typeOf: missing type of variable " ++ name



-- | Generic type instantiation. Produce a new variable for every one generalized over, and substitute
-- it for the old ones in the type and the constraints.
instantiate :: TypeScheme -> Typer (Type, ConstraintSet)
instantiate (TypeScheme refs vars cset typ) = do
  -- Replace the flag references by new ones.
  (typ, cset) <- List.foldl (\rec ref -> do
      (typ, cset) <- rec
      nref <- duplicateFlag ref
      return (subs ref nref typ, subs ref nref cset)
    ) (return (typ, cset)) refs
  -- Replace the type variables.
  List.foldl (\rec var -> do
      (typ, cset) <- rec
      nvar <- runCore freshType
      return (subs var (TypeVar nvar) typ, subs var (TypeVar nvar) cset)
    ) (return (typ, cset)) vars


---------------------------------------------------------------------------------------------------
-- * Printing.

-- | A list of names to be used to represent type variables.
availableNames :: [String]
availableNames = ["a", "b", "c", "d", "a0", "a1", "a2", "b0", "b1", "b2"]

-- | A list of names to be used to represent flag variables.
availableFlags :: [String]
availableFlags = ["n", "m", "p", "q", "n0", "n1", "n2", "m0", "m1", "m2"]


-- | Pre-defined type variable printing function. The variables that may appear in the final type
-- must be given as argument. Each one of these variables is then associated with a name (of the
-- list 'Monad.Core.availableNames'). If too few names are given, the remaining variables are
-- displayed as: prevar \'X\' x.
displayTypeVar :: [Variable] -> Typer (Variable -> String)
displayTypeVar vars = do
  let attr = List.zip vars availableNames
  return $ \x ->
      case List.lookup x attr of
        Just n -> n
        Nothing -> prevar "X" x

-- | Pre-defined flag printing function. It looks up the value of the flags, and display \"!\"
-- if the value is one, and \"\" else.
displayFlag :: Typer (Flag -> String)
displayFlag = do
  flags <- gets flags
  return $ \f ->
      case f of
        1 -> "!"
        0 -> ""
        _ ->
          case IntMap.lookup f flags of
            Just FlagInfo { flagValue = One } -> "!"
            _ -> ""

-- | Display a reference flag. This function is similar to 'Monad.Typer.displayFlag', but
-- displays the reference flag when the value is unknown. The argument gives the reference flags
-- that may appear in the final type. Each reference is then associated with a name.
displayRefFlag :: [Flag] -> Typer (Flag -> String)
displayRefFlag flags = do
  let attr = List.zip flags availableFlags
  flags <- gets Monad.Typer.flags
  return $ \f ->
      case f of
        1 -> "!"
        0 -> ""
        _ ->
          case IntMap.lookup f flags of
            Just FlagInfo { flagValue = One } -> "!"
            Just FlagInfo { flagValue = Zero } -> ""
            _ ->
              case List.lookup f attr of
                Just name -> "(" ++ name ++ ")"
                Nothing -> "(" ++ show f ++ ")"


-- | Type variables are attributed random names before being printed, and the flags are
-- printed with their actual value: only if the flag is set will it be displayed as '!', else it will appear as ''.
printType :: Type -> Typer String
printType typ = do
  pVar <- displayTypeVar $ IntSet.toList $ freevar typ
  pFlag <- displayFlag
  pUser <- runCore displayUserType
  return $ genprint Inf [pFlag, pVar, pUser] typ


-- | Like 'printType', but for linear types.
printLinearType :: LinearType -> Typer String
printLinearType typ = do
  pVar <- displayTypeVar $ IntSet.toList $ freevar typ
  pFlag <- displayFlag
  pUser <- runCore displayUserType
  return $ genprint Inf [pFlag, pVar, pUser] typ


-- | Like 'printType', but for typing schemes.
printScheme :: TypeScheme -> Typer String
printScheme scheme @ (TypeScheme flags vars cset typ) = do
  pVar <- displayTypeVar vars
  pFlag <- displayFlag
  pUser <- runCore displayUserType
  return $ genprint Inf [pFlag, pVar, pUser] scheme


-- | Print the source expression of a constraint.
printSourceExpr :: ConstraintSource -> Typer (Extent, String)
printSourceExpr (InExpr e) = do
  e' <- runCore $ printExpr e
  return (extent $ exprInfo e, e')
printSourceExpr (InPattern p) = do
  p' <- runCore $ printPattern p
  return (extent $ patternInfo p, p')
printSourceExpr Unidentified = return (unknownExtent, "<no location>")


---------------------------------------------------------------------------------------------------
-- * Errors.


-- | Throw a typing error, based on the reference flags of the faulty types.
throwTypingError :: Type -> Type -> ConstraintInfo -> Typer a
throwTypingError t u info = do
  -- Print the types t and u.
  t' <- printType t
  u' <- printType u
  -- Get the location / expression.
  (ext, expr) <- printSourceExpr $ sourceExpr info
  -- Get the original type.
  original <- case sourceType info of
      Just a -> do
        p <- printType a
        return $ Just p
      Nothing -> return Nothing
  -- Check which of the type is the actual one.
  if actual info then throwNE (DetailedTypingError t' u' original expr) ext
  else throwNE (DetailedTypingError u' t' original expr) ext


-- | Throw a non-duplicability error, based on the faulty reference flag.
throwNonDuplicableError :: ConstraintInfo -> Typer a
throwNonDuplicableError info = do
  (ext, expr) <- printSourceExpr $ sourceExpr info
  throwNE (NonDuplicableError expr Nothing) ext


---------------------------------------------------------------------------------------------------
-- * Lifting.

log :: Int -> String -> Typer ()
log lvl msg = lift $ Core.log lvl msg

warning :: Warning -> Maybe Extent -> Typer ()
warning warn ext = lift $ Core.warning warn ext

runCore :: Core a -> Typer a
runCore computation = lift $ computation

runIO :: IO a -> Typer a
runIO computation = runCore $ lift computation
