
module Interpret (-- Only the main function is accessible
                  run) where

import Classes
import Localizing
import qualified Utils

import QpState
import CoreSyntax
import Printer

import Values
import Gates

import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap
import qualified Data.List as List

type Environment = IntMap Value

-- Extract the bindings from a [let .. = .. in ..] construction, and adds them to the environment
bind_pattern :: Pattern -> Value -> Environment -> QpState Environment
----------------------------------------------------------------------
bind_pattern (PVar x) v env = do
  return $ IMap.insert x v env

bind_pattern (PPair p1 p2) (VPair v1 v2) env = do
  ev <- bind_pattern p1 v1 env
  bind_pattern p2 v2 ev

bind_pattern PUnit VUnit env = do
  return env

bind_pattern (PLocated p ex) v env = do
  set_location ex
  bind_pattern p v env

bind_pattern p q env = do
  fail ("Unmatching patterns : " ++ sprint p ++ " and " ++ sprint q)



-- Extract the bindings from a circuit application
bind :: Value -> Value -> QpState [(Int, Int)]
--------------------------------------
bind (VQbit q1) (VQbit q2) = do
  return [(q1, q2)]

bind (VPair v1 v2) (VPair v1' v2') = do
  b1 <- bind v1 v1'
  b2 <- bind v2 v2'
  return (b1 ++ b2)

bind VUnit VUnit = do
  return []

bind v1 v2 = do
  fail ("Unmatching values : " ++ pprint v1 ++ " and " ++ pprint v2)



-- Apply a bind function to a value
apply_binding :: [(Int, Int)] -> Value -> QpState Value
-----------------------------------------
apply_binding b (VQbit q) = do 
  return (VQbit $ Utils.apply_binding b q)

apply_binding b (VPair v1 v2) = do
  v1' <- apply_binding b v1
  v2' <- apply_binding b v2
  return (VPair v1' v2')

apply_binding _ VUnit = do
  return VUnit

apply_binding _ v = do
  fail ("Expected a quantum data value - Actual value : " ++ pprint v)

-- Create a specification (with fresh variables) for a given type
linspec :: LinType -> QpState Value
spec :: Type -> QpState Value
-------------------------------------------
linspec (TLocated t ex) = do
  set_location ex
  linspec t

linspec TQbit = do
  q <- new_id
  return (VQbit q)

linspec (TTensor t1 t2) = do
  q1 <- spec t1
  q2 <- spec t2
  return (VPair q1 q2)

linspec TUnit = do
  return VUnit

linspec t = do
  fail ("Expected a quantum data type - Actual type : " ++ pprint t)

spec (TExp _ t) = linspec t

-- Extract the quantum addresses used in a value
extract :: Value -> QpState [Int]
-------------------------
extract (VQbit q) = do
  return [q]

extract (VPair v1 v2) = do
  q1 <- extract v1
  q2 <- extract v2
  return (q1 ++ q2)

extract VUnit = do
  return []

extract v = do
  fail ("Expected a quantum data value - Actual value : " ++ pprint v)

-------------------------
----- Interpreter -------

-- Evaluate expressions
interpret :: Environment -> Expr -> QpState Value

do_application :: Environment -> Value -> Value -> QpState Value

do_application env f x =
  case (f, x) of
    -- Classical beta reduction
    (VFun closure argp body, _) -> do
        ev <- bind_pattern argp x closure
        interpret ev body

    -- Circuit unboxing
    (VUnbox, _) -> do
        return $ VUnboxed x

    -- Circuit reversal
    (VRev, VCirc t c u) -> do
        return $ VCirc u (rev c) t

    -- Unboxed circuit application
    (VUnboxed (VCirc u c u'), t) -> do
        b <- bind u t
        b' <- unencap c b
        apply_binding b' u'

    -- Circuit boxing
    (VBox typ, _) -> do
        -- Creation of a new specification
        s <- spec typ
        -- Open a new circuit
        ql <- extract s
        c <- open_box ql
        -- Execute the argument, applied to the specification, in the new context
        s' <- do_application env x s
        -- Close the new circuit and reset the old one
        c' <- close_box c
        return (VCirc s c' s')

    _ -> do
        fail ("Expected value of type function - Actual expression : ")


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
    Just v -> return v
    Nothing -> fail $ "Unbound variable " ++ show x 

-- Functions
  -- The current context is enclosed in the function value
interpret env (EFun p e) = do
  return (VFun env p e)

-- Let .. in ..
  -- first evaluate the expr e1
  -- match it with the pattern
  -- evaluate e2 in the resulting context
    -- The state at the end must contains only the bindings from the state at the beginning
interpret env (ELet p e1 e2) = do
  v1 <- interpret env e1
  ev <- bind_pattern p v1 env
  interpret ev e2

-- Function application
interpret env (EApp ef arg) = do
  f <- interpret env ef
  x <- interpret env arg

  do_application env f x


-- Patterns and pattern matching
interpret env (EInjL e) = do
  v <- interpret env e
  return (VInjL v)

interpret env (EInjR e) = do
  v <- interpret env e
  return (VInjR v)

interpret env (EMatch e (p, f) (q, g)) = do
  v <- interpret env e
  case v of
    VInjL w -> do
        ev <- bind_pattern p w env
        interpret ev f

    VInjR w -> do
        ev <- bind_pattern q w env
        interpret ev g

    _ -> fail "Typing error" 



-- Pairs
interpret env (EPair e1 e2) = do
  v1 <- interpret env e1
  v2 <- interpret env e2
  return (VPair v1 v2)

-- If .. then .. else ..
interpret env (EIf e1 e2 e3) = do
  v1 <- interpret env e1
  case v1 of
    VBool True -> do
        interpret env e2
    VBool False -> do
        interpret env e3
    _ -> do
        fail ("Expected value of type bool - Actual expression : " ++ sprint e1)


-------------------
-- Main function --

run :: Expr -> QpState Value
----------------------------
run e = do
  gv <- gate_values
  basic_environment <- return $ IMap.fromList gv
  interpret basic_environment e

