-- | This module implements a small interpreter for Proto-Quipper.
-- This module works along the module "Interpret.Circuits" that provides the definition and operations
-- on circuits. The state of the interpreter is given by a circuit stack in the 'QpState' monad.
-- Each term is interpreted in an evaluation context, which contains the
-- values of all the variables in scope: with this, we don't have to explicitly do the term substitution that comes with beta-reduction.
module Interpret.Interpret where

import Classes
import qualified Utils

import Monad.QuipperError
import Monad.QpState
import Monad.Modules

import Parsing.Location
import Parsing.Syntax (RecFlag (..))
import Parsing.Printer

import Typing.CoreSyntax

import Interpret.Circuits (Circuit, Binding, create_circuit)
import qualified Interpret.Circuits as C
import Interpret.Values

import Control.Exception

import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap
import qualified Data.List as List


-- | The type of the evaluation context.
type Environment = IntMap Value



-- | Generate a fresh quantum address. This is done by incrementing an id in the 'QpState' monad. Note that nothing is done to recycle used and discarded identifiers.
-- However, the index is reinitialized back to 0 at each box creation.
-- Thus, the inputs of a box will always be numbered 0../n/.
fresh_qubit :: QpState Int
fresh_qubit = do
  ctx <- get_context
  q <- return $ qubit_id ctx
  set_context $ ctx { qubit_id = q + 1 }
  return q


-- | Reset the counter of qubit values.
-- Since the quantum addresses are bound in a circuit (/t/, /C/, /u/), we can reset the counter for each box creation.
reset_qubits :: QpState ()
reset_qubits = do
  ctx <- get_context
  set_context $ ctx { qubit_id = 0 }


-- | Return, without incrementing it, the value of the quantum address counter.
last_qubit :: QpState Int
last_qubit = do
  ctx <- get_context
  return $ qubit_id ctx


-- | Set the counter of qubit values.
set_qubits :: Int -> QpState ()
set_qubits q = do
  ctx <- get_context
  set_context $ ctx { qubit_id = q }



-- | Create a specimen of a given linear quantum data type. The quantum addresses of
-- the specimen range from 0 to /n/-1, /n/ being the number of qubits in the type.
linspec :: LinType -> QpState Value
linspec TQubit = do
  q <- fresh_qubit
  return (VQubit q)

linspec (TTensor tlist) = do
  qlist <- List.foldr (\t rec -> do
                         r <- rec
                         q <- spec t
                         return (q:r)) (return []) tlist
  return (VTuple qlist)

linspec TUnit = do
  return VUnit

linspec _ = throw $ ProgramError "linspec: not a quantum data type"

-- | Like 'linspec', but return a specimen of a type.
spec :: Type -> QpState Value
spec (TBang _ t) = linspec t

-- | Create a new circuit, initialized with a set of wire identifiers, and put it on top
-- of the circuit stack.
open_box :: [Int] -> QpState ()
open_box ql = do
  ctx <- get_context
  newc <- return $ create_circuit ql
  set_context $ ctx { circuits = newc:(circuits ctx) }


-- | Unstack and return the top circuit from the circuit stack.
-- The stack must be non empty. An empty circuit stack causes a runtime error.
close_box :: QpState Circuit
close_box = do
  ctx <- get_context
  case circuits ctx of
    [] ->
        throw $ ProgramError "Unsound close box operation"

    (top:rest) -> do
        set_context $ ctx { circuits = rest }
        return top


-- | Append a circuit, using the specified binding. 
-- The action is done on the top circuit. If the circuit list is empty, throw
-- a runtime error. The output of 'unencap' is a binding corresponding to the renaming of the
-- addresses done by the circuit constructor.
unencap :: Circuit -> Binding -> QpState Binding
unencap c b = do
  ctx <- get_context
  case circuits ctx of
    [] -> do
        ex <- get_location
        throw $ ProgramError "empty circuit stack"

    (top:rest) -> do
        (c', b') <- return $ C.unencap top c b
        set_context $ ctx { circuits = (c':rest) }
        return b'


-- | Extract a list of bindings x |-> v by matching a pattern and a value (supposedly of
-- the same type), and insert all of them in the given environment. This function can be called in three
-- different contexts: from a beta reduction (the argument of the function is a pattern), from a let binding,
-- of from a pattern matching.
bind_pattern :: Pattern -> Value -> Environment -> QpState Environment
bind_pattern (PLocated p ex) v env = do
  set_location ex
  bind_pattern p v env

bind_pattern (PConstraint p _) v env = do
  bind_pattern p v env

bind_pattern (PVar x) v env = do
  return $ IMap.insert x v env

bind_pattern (PTuple plist) (VTuple vlist) env = do
  case (plist, vlist) of
    ([], []) ->
        return env

    (p:prest, v:vrest) -> do
        ev <- bind_pattern p v env
        bind_pattern (PTuple prest) (VTuple vrest) ev

    _ ->
        throw $ MatchingError (sprint $ PTuple plist) (sprint $ VTuple vlist)

bind_pattern PUnit VUnit env = do
  return env

bind_pattern (PBool b) (VBool b') env = do
  if b == b' then 
    return env 
    else
    throw $ MatchingError (sprint $ PBool b) (sprint $ VBool b')

bind_pattern (PInt n) (VInt n') env = do
  if n == n' then 
    return env 
    else
    throw $ MatchingError (sprint $ PInt n) (sprint $ VInt n')

bind_pattern (PDatacon dcon p) (VDatacon dcon' v) env = do
  if dcon == dcon' then
    case (p, v) of
      (Just p, Just v) ->
          bind_pattern p v env
      (Nothing, Nothing) ->
          return env
      _ ->
          throw $ MatchingError (sprint $ PDatacon dcon p) (sprint $ VDatacon dcon' v)

  else
    throw $ MatchingError (sprint $ PDatacon dcon p) (sprint $ VDatacon dcon' v)

bind_pattern PWildcard _ env = do
  return env

bind_pattern p v _ = do
  throw $ MatchingError (show p) (sprint v)


-- | Try matching a pattern and a value. Return 'True' if the value matches, else 'False'.
match_value :: Pattern -> Value -> Bool
match_value (PLocated p _) v =
  match_value p v

match_value (PConstraint p _) v =
  match_value p v

match_value PWildcard _ =
  True

match_value (PVar _) _  =
  True

match_value (PTuple plist) (VTuple vlist) = 
  let match_list = (\plist vlist ->
                      case (plist, vlist) of
                        ([], []) ->
                            True
                        (p:prest, v:vrest) ->
                            if match_value p v then
                              match_list prest vrest
                            else
                              False
                        _ ->
                            False) in
  match_list plist vlist

match_value PUnit VUnit =
  True

match_value (PBool b) (VBool b') =
  b == b'

match_value (PInt n) (VInt n') =
  n == n'

match_value (PDatacon dcon p) (VDatacon dcon' v) =
  if dcon == dcon' then
    case (p, v) of
      (Just p, Just v) ->
          match_value p v
      (Nothing, Nothing) ->
          True
      _ ->
          False
  else
    False

match_value _ _ =
  False

-- | Extract the list of associations qubit @\<-\>@ qubit introduced by the matching
-- of two quantum data values.
bind :: Value -> Value -> QpState [(Int, Int)]
bind (VQubit q1) (VQubit q2) = do
  return [(q1, q2)]

bind (VTuple vlist) (VTuple vlist') = do
  case (vlist, vlist') of
    ([], []) ->
        return []
 
    (v:rest, v':rest') -> do
        b <- bind v v'
        brest <- bind (VTuple rest) (VTuple rest')
        return (b ++ brest)

    _ ->
        throw $ MatchingError (sprint $ VTuple vlist) (sprint $ VTuple vlist')

bind VUnit VUnit = do
  return []

bind v1 v2 = do
  throw $ MatchingError (sprint v1) (sprint v2)


-- | Re-address a quantum value using a binding function.
-- If a qubit is not mapped by the binding, its value is left unchanged.
readdress :: Value -> [(Int, Int)] -> QpState Value
readdress (VQubit q) b = do
  case List.lookup q b of
    Just q' ->
        return (VQubit q')
    Nothing ->
        return (VQubit q)

readdress (VTuple vlist) b = do
  vlist' <- List.foldr (\v rec -> do
                          r <- rec
                          v' <- readdress v b
                          return (v':r)) (return []) vlist
  return (VTuple vlist')

readdress VUnit _ = do
  return VUnit

readdress v _ = do
  throw $ ProgramError $ "unsound readdress function application:" ++ pprint v ++ " is not a quantum data value"


-- | Extract the quantum addresses of a value.
extract :: Value -> QpState [Int]
extract (VQubit q) = do
  return [q]

extract (VTuple vlist) = do
  List.foldl (\rec v -> do
                r <- rec
                qv <- extract v
                return $ qv ++ r) (return []) vlist

extract VUnit = do
  return []

extract v = do
   throw $ ProgramError $ "unsound extract function application:" ++ pprint v ++ " is not a quantum data value"



-- | Reduce the application of a function to a value. Several configurations can occur:
--
-- *  beta-reduction, i.e., the reduction of the application of a value to an abstraction. This also includes the built-in function
--    applications.
--
-- *  @(unbox c) t@. Assuming the function is an unboxed circuit (represented by VUnboxed c), applies the 'unencap' function (usual semantics).
--
-- * @unbox c@. Returns the unboxed circuit (i.e., VUnboxed c).
--
-- * @box[T] t@. See the operational semantics for more information about this case.
-- 
-- * @rev c@. Reverses the circuit.
--
-- A dedicated function was needed to reduce the function applications, because the 'Interpret.Interpret.interpret' function only reduces
-- function application of the kind (expr expr), and not (value value). However, the creation of a box implies the application of a function
-- to a newly created quantum data value, which does not fit the type of 'Interpret.Interpret.interpret'.
do_application :: Environment -> Value -> Value -> QpState Value
do_application env f x =
  case (f, x) of
    -- Classical beta reduction
    (VFun closure argp body, _) -> do
        -- The argument pattern and value are bound together, and the resulting bindings added to the environment
        ev <- bind_pattern argp x closure
        -- Evaluation of the body of the function
        interpret ev body

    -- Builtin application
    (VBuiltin bf, _) -> do
        return $ bf x

    -- Circuit unboxing
    (VUnbox, _) -> do
        return $ VUnboxed x

    -- Circuit reversal
    (VRev, VCirc t c u) -> do
        return $ VCirc u (rev c) t

    -- Unboxed circuit application
    (VUnboxed (VCirc u c u'), t) -> do
        -- The argument is bound to the input of the circuit
        b <- bind u t
        -- Append the circuit to the edited one
        b' <- unencap c b
        -- Produces the return value by readdressing the output of the circuit
        readdress u' b'

    -- Unboxed unbuilt circuit : build a new circuit, or rather directly apply the boxed function f to t
    (VUnboxed (VSumCirc f), t) -> do
        do_application env f t

    -- Circuit boxing
    (VBox typ, _) -> do
        -- If the type is classical, the circuit is readily built
        if not $ is_user_type typ then do
          -- Creation of a new specimen of type type, with qubits ranging from 0, 1 .. to n,
          -- n the number of qubits in the type typ
          qinit <- last_qubit
          reset_qubits
          s <- spec typ
          
          -- Open a new circuit, initialized with the quantum addresses of the specimen
          ql <- extract s
          open_box ql
          -- Build the circuit by applying the function argument to the specimen
          s' <- do_application env x s
          -- Close the box, and return the corresponding circuit
          c <- close_box
          
          -- Reset the counter for qubit values
          set_qubits qinit
          return (VCirc s c s')
 
        -- If not, the construction is delayed till use of the box.
        else do
          return (VSumCirc x)

    (VDatacon dcon Nothing, _) ->
        return $ VDatacon dcon $ Just x

    _ -> do
        ex <- get_location
        throw $ LocatedError (NotFunctionError (sprint f)) ex



-- | Evaluate an expression. 
-- Knowing that the monad 'QpState' encloses a circuit stack, this function closely follows the theoretical semantics describing the
-- reduction of a closure [/C/, /t/]. The main difference is that the substitutions done during the beta reduction are delayed via
-- the passing of the environment: only when the function must evaluate a variable is the associated value retrieved.
-- An auxiliary function, 'Interpret.Interpret.do_application', reduces the application of a function value to an argument value.
interpret :: Environment -> Expr -> QpState Value
-- Location handling
interpret env (ELocated e ex) = do
  set_location ex
  interpret env e

interpret _ (EError msg) = do
  throwQ (UserError msg)

-- Empty
interpret _ EUnit = do
  return VUnit

-- Booleans
interpret _ (EBool b) = do
  return (VBool b)

-- Integers
interpret _ (EInt n) = do
  return (VInt n)

-- Constructors
interpret _ EUnbox = do
  return VUnbox

interpret _ ERev = do
  return VRev

interpret _ (EBox typ) = do
  return (VBox typ)

-- Variables
interpret env (EVar x) = do
  case IMap.lookup x env of
    Just v ->
        return v
    Nothing -> do
        -- This kind of errors should have been eliminated during the translation to the internal syntax
        ex <- get_location
        throw $ LocatedError (UnboundVariable (show x)) ex

-- Global variables
interpret env (EGlobal x) = do
  vals <- get_context >>= return . values
  case IMap.lookup x vals of
    Just v ->
        return v
    Nothing -> do
        -- This kind of errors should have been eliminated during the translation to the internal syntax
        ex <- get_location
        throw $ LocatedError (UnboundVariable (show x)) ex


-- Functions : The current context is enclosed in the function value
interpret env (EFun p e) = do
  return (VFun env p e)

-- Let .. in ..
interpret env (ELet r p e1 e2) = do
  -- Reduce the argument e1
  v1 <- interpret env e1
  
  -- Recursive function ?
  case (r, v1, drop_constraints $ clear_location p) of
    (Recursive, VFun ev arg body, PVar x) ->
        let ev' = IMap.insert x (VFun ev' arg body) ev in do
          env <- bind_pattern p (VFun ev' arg body) env
          interpret env e2

    _ -> do
        -- Bind it to the pattern p in the current context
        ev <- bind_pattern p v1 env

        -- Interpret the body e2 in this context
        interpret ev e2

-- Function application
interpret env (EApp ef arg) = do
  f <- interpret env ef
  x <- interpret env arg

  do_application env f x

-- Patterns and pattern matching
interpret env (EDatacon datacon e) = do
  case e of
    Just e -> do
        v <- interpret env e
        return (VDatacon datacon (Just v))

    Nothing ->
        return (VDatacon datacon Nothing)

interpret env (EMatch e blist) = do
  let match = (\ex v blist ->
                 case blist of
                   [] ->
                       throw $ LocatedError (NoMatchError (sprint v)) ex
                   ((p, f):rest) -> do
                       if match_value p v then do
                         ev <- bind_pattern p v env
                         interpret ev f
                       else
                         match ex v rest) in do
    ex <- get_location
    v <- interpret env e
    match ex v blist

-- Pairs
interpret env (ETuple elist) = do
  vlist <- List.foldr (\e rec -> do
                         r <- rec
                         v <- interpret env e
                         return (v:r)) (return []) elist
  return (VTuple vlist)

-- If .. then .. else ..
interpret env (EIf e1 e2 e3) = do
  v1 <- interpret env e1
  case v1 of
    VBool True -> do
        interpret env e2

    VBool False -> do
        interpret env e3

    _ -> do
        ex <- get_location
        throw $ LocatedError (NotBoolError (sprint v1)) ex

interpret env (EConstraint e _) = do
  interpret env e

interpret _ (EBuiltin s) =
  builtin_value s




