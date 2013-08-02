module Interpret.Interpret (-- Only the main function is accessible
                  run_module) where

import Classes
import qualified Utils

import Monad.QuipperError
import Monad.QpState
import Monad.Modules

import Parsing.Localizing
import Parsing.Syntax (RecFlag (..))
import Parsing.Printer

import Typing.CoreSyntax

import Interpret.Circuits (Circuit (..), Binding)
import qualified Interpret.Circuits as C
import Interpret.Values

import Control.Exception

import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap
import qualified Data.List as List


type Environment = IntMap Value


-- | Return fresh quantum address
fresh_qbit :: QpState Int
fresh_qbit = do
  ctx <- get_context
  q <- return $ qbit_id ctx
  set_context $ ctx { qbit_id = q + 1 }
  return q


-- | Reset the counter of qbit values
reset_qbits :: QpState ()
reset_qbits = do
  ctx <- get_context
  set_context $ ctx { qbit_id = 0 }


-- | Create a specimen of a given type / linear type. The quantum addresses of
-- the specimen range from 0 .. to n, n being the number of qbits in the type
-- The axiliary function keeps track of the counter
linspec :: LinType -> QpState Value
linspec (TLocated t ex) = do
  set_location ex
  linspec t

linspec TQbit = do
  q <- fresh_qbit
  return (VQbit q)

linspec (TTensor tlist) = do
  qlist <- List.foldr (\t rec -> do
                         r <- rec
                         q <- spec t
                         return (q:r)) (return []) tlist
  return (VTuple qlist)

linspec TUnit = do
  return VUnit


spec :: Type -> QpState Value
spec (TBang _ t) = linspec t


-- | Modifiers of qpState specififc to circuit construction
-- It only relays the functions unencap, open and close box of the circuit
-- class

-- | Stack on a new circuit, initialized with the list a qbits as wires
open_box :: [Int] -> QpState ()
open_box ql = do
  ctx <- get_context
  newc <- return $ Circ { qIn = ql, gates = [], qOut = ql }
  set_context $ ctx { circuits = newc:(circuits ctx) }


-- | Unstack and returns the top circuit
-- The list must be non empty. An empty circuit list correspond to a program error (as close_box is called only after
-- an open_box)
close_box :: QpState Circuit
close_box = do
  ctx <- get_context
  case circuits ctx of
    [] ->
        throw $ ProgramError "Unsound close box operation"

    (top:rest) -> do
        set_context $ ctx { circuits = rest }
        return top


-- | Append a circuit, the welding specified by the argument binding
-- The action is done on the top circuit. If the circuit list is empty, it corresponds to
-- a runtime error. The output of unencap is a binding corresponding to the renaming of the
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


-- | Extract the list of bindings x |-> v from a matching between a pattern and a value (supposedly of
-- the same type, and insert all of them in the given environment. This function can be called in three
-- diffrent contexts : from a beta reduction (the argument of the function is a pattern), from a let binding,
-- of from a pattern matching
bind_pattern :: Pattern -> Value -> Environment -> QpState Environment
bind_pattern (PLocated p ex) v env = do
  set_location ex
  bind_pattern p v env

bind_pattern (PVar x) v env = do
  -- If the var is global, update the module definition
  cm <- get_module
  set_module $ cm { global_vars = IMap.update (\_ -> Just v) x $ global_vars cm }

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

bind_pattern p v _ = do
  throw $ MatchingError (sprint p) (sprint v)


-- | Try matching a pattern and a value. Return True if the value matches, else False
match_value :: Pattern -> Value -> Bool
match_value (PLocated p _) v =
  match_value p v

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

-- | Extract the list of associations qbit <-> qbit introduced by the matching
-- of the two argument values
bind :: Value -> Value -> QpState [(Int, Int)]
bind (VQbit q1) (VQbit q2) = do
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


-- | Readdress a quantum value following a binding function
-- If a qbit is not mapped by the binding, its value is left unchanged
readdress :: Value -> [(Int, Int)] -> QpState Value
readdress (VQbit q) b = do
  case List.lookup q b of
    Just q' ->
        return (VQbit q')
    Nothing ->
        return (VQbit q)

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


-- | Extract the quantum addresses of a value
extract :: Value -> QpState [Int]
extract (VQbit q) = do
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



-- | Implementation of the evaluation of an expression. The main function, interpret, has type Environment -> Expr -> QpState Value
-- Knowing that the monad QpState encloses a circuit stack, the prototype is close to the theoretical semantics describing the
-- reduction of the closure [C, t]. The main difference is that the substitutions done during the beta reduction are delayed via
-- the passing of the environment : only when the function must evaluate a variable is the associated value retrieved.
-- An auxiliary function, do_application, reduces the application of a function value to an argument value.

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

    -- Circuit boxing
    (VBox typ, _) -> do
        -- Creation of a new specimen of type type, with qbits ranging from 0, 1 .. to n,
        -- n the number of qbits in the type typ
        reset_qbits
        s <- spec typ
        -- Open a new circuit, initialized with the quantum addresses of the specimen
        ql <- extract s
        open_box ql
        -- Build the circuit by applying the function argument to the specimen
        s' <- do_application env x s
        -- Close the box, and return the corresponding circuit
        c <- close_box
        return (VCirc s c s')

    (VDatacon dcon Nothing, _) ->
        return $ VDatacon dcon $ Just x

    _ -> do
        ex <- get_location
        file <- get_file
        throw $ NotFunctionError (sprint f) (file, ex)



interpret :: Environment -> Expr -> QpState Value
-- Location handling
interpret env (ELocated e ex) = do
  set_location ex
  interpret env e

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
  case typ of
    TForall _ _ _ typ ->
        return (VBox typ)
    _ ->
        return (VBox typ)

-- Variables
interpret env (EVar x) = do
  case IMap.lookup x env of
    Just v ->
        return v
    Nothing -> do
        -- This kind of errors should have been eliminated during the translation to the internal syntax
        ex <- get_location
        file <- get_file
        throw $ UnboundVariable (show x) (file, ex)

-- Global variables
interpret env (EGlobal x) = do
  case IMap.lookup x env of
    Just v ->
        return v
    Nothing -> do
        -- This kind of errors should have been eliminated during the translation to the internal syntax
        ex <- get_location
        file <- get_file
        throw $ UnboundVariable (show x) (file, ex)


-- Functions : The current context is enclosed in the function value
interpret env (EFun p e) = do
  return (VFun env p e)

-- Let .. in ..
interpret env (ELet r p e1 e2) = do
  -- Reduce the argument e1
  v1 <- interpret env e1
  
  -- Recursive function ?
  case (r, v1, p) of
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
                       throw $ NoMatchError (sprint v) ex
                   ((p, f):rest) -> do
                       if match_value p v then do
                         ev <- bind_pattern p v env
                         interpret ev f
                       else
                         match ex v rest) in do
    ex <- get_location
    f <- get_file
    v <- interpret env e
    match (f, ex) v blist

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
        f <- get_file
        throw $ NotBoolError (sprint v1) (f, ex)

interpret env (EConstraint e _) = do
  interpret env e

interpret _ (EBuiltin s) =
  builtin_value s



-- | Main function, the only one to be called outside of the module
-- The interpret function is launched with a basic environment containing only
-- the gate values
run_module :: Expr -> QpState Value
run_module e = do
  -- Create the initial evaluation context
  gbls <- global_context

  -- Reset the circuit stack
  ctx <- get_context
  set_context $ ctx { circuits = [Circ { qIn = [], gates = [], qOut = [] }] }

  interpret gbls e

