-- | This module implements a small interpreter for Proto-Quipper. This module works along the module
-- "Interpreter.Circuits" that provides the definition and operations on circuits. The state of the
-- interpreter is given by a circuit stack in the 'Interpreter' monad. Each term is interpreted in an
-- evaluation context, which contains the values of all the variables in scope: with this, we don't
-- have to explicitly do the term substitution that comes with beta-reduction.
module Interpreter.Interpreter where

import Classes
import Utils
import Options (circuitFormat)
import Parsing.Location

import Monad.Error
import Monad.Core (variableName, getOptions, printValue)
import Monad.Typer (resolveType, printType)
import Monad.Interpreter

import Core.Syntax

import Interpreter.Circuits as Circuits (rev, Circuit)
import Interpreter.Values
import Interpreter.IRExport

import Data.IntMap as IntMap
import Data.List as List

import Control.Monad.Trans


-- | The type of the evaluation context.
type Environment = IntMap Value


-- | Create a specimen of a given quantum data type. The quantum addresses of the specimen range
-- from 0 to /n/-1, /n/ being the number of qubits in the type.
specimen :: Type -> Interpreter Value
specimen (TypeAnnot _ t) = linspec t
  where
    linspec :: LinearType -> Interpreter Value
    linspec (TypeApply (TypeBuiltin "qubit") _) = do
      q <- freshQubit
      return $ VQubit q
    linspec (TypeApply (TypeBuiltin "*") tensor) = do
      qlist <- List.foldr (\t rec -> do
          qlist <- rec
          q <- specimen t
          return $ q:qlist) (return []) tensor
      return $ VTuple qlist
    linspec (TypeApply (TypeBuiltin "unit") _) =
      return $ VConstant ConstUnit
    linspec _ = fail "Interpret:linspec: illegal argument"


-- | Extract a list of bindings x |-> v by matching a pattern and a value (supposedly of the same
-- type), and insert all of them in the given environment. This function can be called in three
-- different contexts: from a beta reduction (the argument of the function is a pattern), from a let
-- binding, of from a pattern matching.
bindPattern :: Pattern -> Value -> Environment -> Environment
bindPattern (PCoerce p _ _) v env = bindPattern p v env
bindPattern (PWildcard _) _ env = env
bindPattern (PVar _ x) v env = IntMap.insert x v env
bindPattern p @ (PConstant _ c) v @ (VConstant c') env =
  if c == c' then env
  else throwNE $ MatchingError (sprint p) (sprint v)

bindPattern p @ (PTuple _ ptuple) v @ (VTuple vtuple) env =
  if List.length ptuple /= List.length vtuple then throwNE $ MatchingError (sprint p) (sprint v)
  else List.foldl (\env (p, v) -> bindPattern p v env) env $ List.zip ptuple vtuple

bindPattern p @ (PDatacon info cons parg) v @ (VDatacon cons' varg) env =
  if cons == cons' then
    case (parg, varg) of
      (Just p, Just v) -> bindPattern p v env
      (Nothing, Nothing) -> env
      _ -> throwNE $ MatchingError (sprint p) (sprint v)
  else throwNE $ MatchingError (sprint p) (sprint v)

bindPattern p v _ = throwNE $ MatchingError (sprint p) (sprint v)


-- | Try matching a pattern and a value. Return 'True' iff the value matches.
matchValue :: Pattern -> Value -> Bool
matchValue (PCoerce p _ _) v = matchValue p v
matchValue (PWildcard _) _ = True
matchValue (PVar _ _) _  = True
matchValue (PConstant _ c) (VConstant c') = c == c'
matchValue (PTuple _ ptuple) (VTuple vtuple) =
  if (List.length ptuple /= List.length vtuple) then False
  else List.and $ List.map (\(p, v) -> matchValue p v) $ List.zip ptuple vtuple
matchValue (PDatacon _ cons p) (VDatacon cons' v) =
  if cons == cons' then
    case (p, v) of
      (Just p, Just v) -> matchValue p v
      (Nothing, Nothing) -> True
      _ -> False
  else False
matchValue _ _ = False


-- | Extract the list of associations qubit @\<-\>@ qubit introduced by the matching of two quantum
-- data values.
bindQuantum :: Value -> Value -> [(Int, Int)]
bindQuantum v v' = bind [] v v'
  where
    bind :: [(Int, Int)] -> Value -> Value -> [(Int, Int)]
    bind map (VQubit q) (VQubit q') = (q, q'):map
    bind map v @ (VTuple tuple) v' @ (VTuple tuple') = do
      if (List.length tuple /= List.length tuple') then throwNE $ MatchingError (sprint v) (sprint v')
      else List.foldl (\map (v, v') -> bind map v v') map $ List.zip tuple tuple'
    bind map (VConstant ConstUnit) (VConstant ConstUnit) = map
    bind _ v v' = do
      throwNE $ MatchingError (sprint v) (sprint v')


-- | Re-address a quantum value using a binding function. If a qubit is not mapped by the binding,
-- its value is left unchanged.
readdress :: [(Int, Int)] -> Value -> Value
readdress map (VQubit q) =
  case List.lookup q map of
    Just q' -> VQubit q'
    Nothing -> VQubit q
readdress map (VTuple tuple) = VTuple $ List.map (readdress map) tuple
readdress _ v = v


-- | Extract the quantum addresses of a value.
extract :: Value -> [Int]
extract (VQubit q) = [q]
extract (VTuple tuple) = List.concat $ List.map extract tuple
extract _ = []


-- | Reduce the application of a function to a value. Several configurations can occur:
--
-- * beta-reduction, i.e., the reduction of the application of a value to an abstraction. This also
--   includes the built-in function applications.
--
-- * @(unbox c) t@. Assuming the function is an unboxed circuit (represented by VUnboxed c), applies
--   the 'unencap' function (usual semantics).
--
-- * @unbox c@. Returns the unboxed circuit (i.e., VUnboxed c).
--
-- * @box[T] t@. See the operational semantics for more information about this case.
--
-- * @rev c@. Reverses the circuit.
--
-- A dedicated function was needed to reduce the function applications, because the
-- 'Interpreter.Interpreterer.interpret' function only reduces function application of the kind
-- (expr expr), and not (value value). However, the creation of a box implies the application of a
-- function to a newly created quantum data value, which does not fit the type of
-- 'Interpreter.Interpreterer.interpret'.
reduceApplication :: Environment -> Value -> Value -> Interpreter Value
reduceApplication env f arg =
  case (f, arg) of
    -- Classical beta reduction. The argument pattern and value are bound together, and the resulting
    -- bindings are added to the function closure (the external environment is not used here).
    (VFun closure binder body, _) -> do
      let env = bindPattern binder arg closure
      interpret env body

    -- Builtin application.
    (VBuiltin builtin, _) -> return $ builtin arg
    -- Data constructors are also functions.
    (VDatacon cons Nothing, _) -> return $ VDatacon cons $ Just arg

    -- Circuit unboxing.
    (VUnbox, _) -> return $ VUnboxed arg
    -- Circuit reversal.
    (VRev, VCirc t c u) -> return $ VCirc u (Circuits.rev c) t
    -- Unboxed circuit application: bind the argument to the input of the circuit, and call the
    -- circuit unencap function (from the interpreter monad). Then readdress the output of the circuit
    -- using the returned qubit mapping.
    (VUnboxed (VCirc u c u'), t) -> do
      map' <- unencap c $ bindQuantum u t
      return $ readdress map' u'
    -- Circuit boxing.
    (VBox typ, _) -> do
      -- Creation of a new specimen of type type, with qubits ranging from 0, 1 .. to n, n the
      -- number of qubits in the type typ.
      qinit <- lastQubit
      resetQubit
      input <- specimen typ
      -- Open a new circuit, initialized with the quantum addresses of the specimen.
      let wires = extract input
      openBox wires
      -- Build the circuit by applying the function argument to the specimen.
      output <- reduceApplication env arg input
      -- Close the box, and return the corresponding circuit.
      circ <- closeBox
      -- Reset the state to its previous configuration.
      setQubit qinit
      return $ VCirc input circ output

    -- The function was called with something not a function: unreducable application.
    _ -> throwWE (NotFunctionError (sprint f)) unknownExtent



-- | Evaluate an expression. Knowing that the monad 'Interpreter' encloses a circuit stack, this
-- function closely follows the theoretical semantics describing the reduction of a closure [/C/, /t/].
-- The main difference is that the substitutions done during the beta reduction are delayed via the
-- passing of the environment: only when the function must evaluate a variable is the associated value
-- retrieved. An auxiliary function, 'Interpreter.Interpreterer.reduceApplication', reduces the
-- application of a function value to an argument value.
interpret :: Environment -> Expr -> Interpreter Value
-- Simple translations.
interpret _ (EError msg) = throwNE $ UserError msg
interpret _ (EConstant _ c) = return $ VConstant c
interpret _ (EUnbox _) = return VUnbox
interpret _ (ERev _) = return VRev
interpret _ (EBox _ typ) = return $ VBox typ

-- Variables: the value should be in the environment.
interpret env (EVar info x) = do
  case IntMap.lookup x env of
    Just v -> return v
    Nothing -> do
      -- This kind of errors should have been eliminated during the translation to the internal syntax.
      name <- runCore $ variableName x
      throwWE (UnboundVariable name) $ extent info

-- Global variables, their values have to be retrieved from the module dependencies.
interpret env (EGlobal _ x) = getValue x

-- Functions : The current context is enclosed in the function value.
interpret env (EFun _ binder body) = return $ VFun env binder body

-- Let bindings.
interpret env (ELet r binder value seq) = do
  value' <- interpret env value -- Reduce the bound value.
  -- If the function is recursive, its value is manually added to the closure.
  case (r, value', uncoerce binder) of
    (Recursive, VFun closure arg body, PVar _ x) -> do
      let closure' = IntMap.insert x (VFun closure' arg body) closure -- Recursive data construction ...
      let env' = bindPattern binder (VFun closure' arg body) env
      interpret env' seq
    _ -> do
      let env' = bindPattern binder value' env
      interpret env' seq

-- Function application.
interpret env (EApp f arg) = do
  f' <- interpret env f
  arg' <- interpret env arg
  reduceApplication env f' arg'

-- Data constructors.
interpret env (EDatacon _ cons arg) = do
  case arg of
    Just arg -> do
      arg' <- interpret env arg
      return $ VDatacon cons $ Just arg'
    Nothing ->
      return $ VDatacon cons Nothing

-- Pattern matching.
interpret env (EMatch info test cases) = do
  test' <- interpret env test
  match test' cases
  where
    match :: Value -> [Binding] -> Interpreter Value
    match test [] = throwWE (NoMatchError (sprint test)) $ extent info
    match test ((Binding binder e):cases) =
      if matchValue binder test then do
        let env' = bindPattern binder test env
        interpret env' e
      else
        match test cases

-- Tuples.
interpret env (ETuple _ tuple) = do
  tuple' <- List.foldr (\e rec -> do
      tuple <- rec
      v <- interpret env e
      return $ v:tuple) (return []) tuple
  return $ VTuple tuple'

-- Conditionals.
interpret env (EIf test btrue bfalse) = do
  test' <- interpret env test
  case test' of
    VConstant (ConstBool True) -> interpret env btrue
    VConstant (ConstBool False) -> interpret env bfalse
    _ -> throwWE (NotBoolError (sprint test')) unknownExtent

interpret env (ECoerce e _) = interpret env e


-- | Evaluate a toplevel declaration.
interpretDeclaration :: Bool -> Environment -> Declaration -> Interpreter Environment
interpretDeclaration False env (DExpr _ _) = return env
interpretDeclaration _ env (DExpr info value) = do
  v <- interpret env value
  pv <- runCore $ printValue v
  options <- runCore getOptions
  typ <- runTyper $ resolveType $ typ info
  inferred <- runTyper $ printType typ
  case (v, circuitFormat options) of
    (VCirc _ c _, "ir") -> runCore $ lift $ putStrLn $ export_to_IR c
    (VCirc _ c _, "visual") -> runCore $ lift $ putStrLn (pprint c ++ " : " ++ inferred)
    _ -> runCore $ lift $ putStrLn (pv ++ " : " ++ inferred)
  return env

interpretDeclaration _ env (DLet info rec x value) = do
  value <- interpret env value -- Reduce the value.
  -- Recursive function ?
  return $ case (rec, value) of
      (Recursive, VFun closure arg body) ->
        let closure' = IntMap.insert x (VFun closure' arg body) closure in -- Recursive closure.
        IntMap.insert x (VFun closure' arg body) env
      _ -> IntMap.insert x value env


-- | Interpret a list of declarations.
interpretDeclarations :: Bool -> [Declaration] -> Interpreter Environment
interpretDeclarations toplevel declarations = do
  List.foldl (\rec declaration -> do
      env <- rec
      interpretDeclaration toplevel env declaration
    ) (return IntMap.empty) declarations
