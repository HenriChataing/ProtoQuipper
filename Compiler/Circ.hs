-- | This module defines methods that shall be used to generate the functions of the quantum library.
-- Amongst others, a function to generate the code of box[T] given a certain type T, the code of unbox[T,U] given some types T and U, and
-- so on. New builtin operations are introduced that will replace the box, unbox and rev operators:
--
-- * @OPENBOX@: takes the number of quantum addresses to give to the new circuit.
--
-- * @CLOSEBOX@: returns the circuit from the top of the stack.
--
-- * @REV@: inputs a circuit and outputs the reverse circuit.
--
-- * @UNENCAP@: inputs a binding and a circuit, and appends this circuit to the one on top of the stack. It returns a binding that gives the renaming
-- of the ouput wires.
--
module Compiler.Circ where

import Classes
import Utils

import Monad.QpState
import Monad.QuipperError

import Compiler.SimplSyntax

import Interpret.Circuits (unary_gates, binary_gates)

import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map


-- | Give the implementation of the unbox operator.
implement_unbox :: (QType, QType)        -- ^ The type of the input circuit.
                -> QpState Expr          -- ^ The code (function) implementation of the unbox operator for the given type.
implement_unbox (t, u) = do
  -- Creation of auxiliary variables
  x0 <- create_var "cc"
  x1 <- create_var "q"
  xt <- create_var "t"
  xu <- create_var "u"
  xc <- create_var "c"
  xb <- create_var "b"
  xb' <- create_var "b"

  -- Implementation of the chunks of code needed for the bindings
  (elet, b) <- implement_bind t x1 xt
  (elet', v) <- implement_appbind u xb' xu

  return $ EFun x0 $ EFun x1 $
        -- Extract the information from the argument
        ELet xt (EAccess 0 x0) $
        ELet xc (EAccess 1 x0) $
        ELet xu (EAccess 2 x0) $
        -- Build the binding
        elet $ ELet xb b $
        -- Call the unencap function
        ELet xb' (EApp (EApp (EBuiltin "UNENCAP") (EVar xb)) (EVar xc)) $
        -- Finally, apply the binding to the output value
        elet' $ v


-- | Give the implementation of the box[T] operator.
implement_box :: QType                   -- ^ The type of the input value.
              -> QpState Expr            -- ^ The code (function) implementation of the box[T] operator.
implement_box typ = do
  -- The code used to generate the specimen
  (spec, n) <- implement_spec typ

  -- Creation of some variables
  x0 <- create_var "f"
  x1 <- create_var "t"
  x2 <- create_var "u"
  x3 <- create_var "c"

  -- Implementation of box[T]
  return $ EFun x0 $
        ELet x1 spec $                                -- Create the specimen
        ESeq (EApp (EBuiltin "OPENBOX") (EInt n)) $   -- Open a new box
        ELet x2 (EApp (EVar x0) (EVar x1)) $          -- Apply the argument function to the specimen
        ELet x3 (EBuiltin "CLOSEBOX") $               -- Close the box
        ETuple [EVar x1, EVar x3, EVar x2]            -- Build the resulting circuit


-- | Produce the implementation of the rev operator. The implementation doesn't need the type of rev.
-- The function implemented takes in a circuit of the form @(t, c, u)@ and returns @(u, c-1, t)@
implement_rev :: QpState Expr
implement_rev = do
  -- Creation of the variables needed to define the function
  x0 <- create_var "cc"
  x1 <- create_var "t"
  x2 <- create_var "c"
  x3 <- create_var "u"

  -- Implementation of the function
  return $ EFun x0 $
        ELet x1 (EAccess 0 x0) $
        ELet x2 (EAccess 1 x0) $
        ELet x3 (EAccess 2 x0)
        (ETuple [EVar x3, EApp (EBuiltin "REV") (EVar x2), EVar x1])


-- | Generate the code of the @spec[T]@ value. Be aware that @spec[T]@ is not a function, but instead a pair @(v, n)@
-- where @v@ is a specimen of the type @T@ (with quantum addresses numbered from 0 to |qubit|-1) and @n@ the number of qubits
-- used.
implement_spec :: QType -> QpState (Expr, Int)
implement_spec typ = do
  return $ spec_n typ 0
  where  
    spec_n QQubit n = (EInt n, n+1)
    spec_n QUnit n = (EUnit, n)
    spec_n (QTensor qlist) n =
      let (qlist', n') = List.foldl (\(ql, n) q ->
            let (q', n') = spec_n q n in
            (q':ql, n')) ([], n) qlist in
      (ETuple $ List.reverse qlist', n')
    spec_n _ _ =
          throwNE $ ProgramError "QLib:spec_n: illegal argument"


-- | Generate the code that binds the quantum addresses of two variables of type the given one.
-- The genrated binding will be of the form:
--
-- * (0) if no variables can be bound.
--
-- * (1, x, x', b) if x is bound to x' (and b is the rest of the binding).
--
-- The other element contains the variable allocations.
implement_bind :: QType -> Variable -> Variable -> QpState (Expr -> Expr, Expr)
implement_bind typ x y = do
  (elet, b) <- bind typ x y
  -- Build both the final binding and let-bindings
  let b' = List.foldl (\e (x, y) -> ETuple [EInt 1, EVar x, EVar y, e]) (ETuple [EInt 0]) b
  let elet' = List.foldr (\(x, ex) e ->
        \f -> e (ELet x ex f)) (\f -> f) elet
  return (elet', b')
 
  where
    -- The bind function returns a pairs (elet, b) where elet contains the variable creations, and b the bindings
    bind QQubit x y =
      return $ ([], [(x,y)])
    bind QUnit _ _ =
      return $ ([], [])
    bind (QTensor qlist) x y =
      List.foldl (\rec (n, q) -> do
            (elet, b) <- rec
            -- Test beforehand to known whether q holds some qubits
            if has_qubits q then do
              -- Yes: extract the nth element of x and y, and apply the function recursively
              xn <- create_var "x"
              yn <- create_var "y"
              (elet', b') <- bind q xn yn
              return (elet ++ [(xn, EAccess n x), (yn, EAccess n y)] ++ elet', b' ++ b)
            else
              -- No: do nothing
              return (elet, b)) (return ([], [])) (List.zip [0..List.length qlist-1] qlist)

    bind _ _ _ =
      fail "QLib:bind: illegal argument"


-- | Generate the code that apply a binding to a quantum value of type the given one.
implement_appbind :: QType -> Variable -> Variable -> QpState (Expr -> Expr, Expr)
implement_appbind typ b x = do
  (elet, e) <- appbind typ x
  -- Build the series of instructions
  let elet' = List.foldr (\(x, ex) e ->
        \f -> e (ELet x ex f)) (\f -> f) elet
  return (elet', e)

  where
    -- In the following, b is expected of the form : EApp (EBuiltin "APPBIND") b where is a binding
    appbind QUnit _ = return ([], EUnit)
    appbind QQubit x = return ([], EApp (EApp (EBuiltin "APPBIND") (EVar b)) (EVar x))
    appbind (QTensor qlist) x = do
      (elet, elist) <- List.foldl (\rec (n, q) -> do
            (elet, elist) <- rec
            -- Test beforehand to known whether q holds some qubits
            if has_qubits q then do
              -- Yes: extract the nth element of x, and apply the function recursively
              xn <- create_var "x"
              (elet', e') <- appbind q xn
              return (elet ++ [(xn, EAccess n x)] ++ elet', e':elist)
            else
              -- No: do nothing
              return (elet, (EAccess n x):elist)) (return ([], [])) (List.zip [0..List.length qlist-1] qlist)
      return (elet, ETuple $ List.reverse elist)
    appbind _ _ =
      fail "QLib:appbind: illegal argument"



-- | Request for an implementation of the unbox operator of type T, U. A reference to the implementation is passed as argument.
request_unbox :: CircType -> QpState Variable
request_unbox c = do
  ctx <- get_context
  let ql = circOps ctx
  case Map.lookup c $ unboxes ql of
    Just x ->
        return x
    Nothing -> do
        -- Implement the needed operator, and upload it to the circOps library.
        x <- create_var "unbox"
        eunbox <- implement_unbox c
        let ql' = ql {
              unboxes = Map.insert c x $ unboxes ql,
              code = (DLet x eunbox):(code ql)
            }
        ctx <- get_context
        set_context ctx { circOps = ql' }
        return x


-- | Request for an implementation of the box operator of type T. A reference to the implementation is passed as argument.
request_box :: QType -> QpState Variable
request_box t = do
  ctx <- get_context
  let ql = circOps ctx
  case Map.lookup t $ boxes ql of
    Just x ->
        return x
    Nothing -> do
        -- Implement the needed operator, and upload it to the circOps library.
        x <- create_var "box"
        ebox <- implement_box t
        let ql' = ql {
              boxes = Map.insert t x $ boxes ql,
              code = (DLet x ebox):(code ql)
            }
        ctx <- get_context
        set_context ctx { circOps = ql' }
        return x


-- | Request for an implementation of the rev operator.
request_rev :: QpState Variable
request_rev = do
  ctx <- get_context
  let ql = circOps ctx
  case rev ql of
    Just x ->
        return x
    Nothing -> do
        -- Implement the needed operator, and upload it to the circOps library.
        x <- create_var "rev"
        erev <- implement_rev
        let ql' = ql {
              rev = Just x,
              code = (DLet x erev):(code ql)
            }
        ctx <- get_context
        set_context ctx { circOps = ql' }
        return x



