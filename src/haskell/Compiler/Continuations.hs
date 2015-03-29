{-# LANGUAGE MultiParamTypeClasses #-}

-- | This module contains the definition of the last language used before the construction of the
-- LLVM module. It explicitates the flow control, under the form of continuation expressions. Language
-- operators are close to those used in LLVM-IR. In particular, data constructors are explicitated into
-- fixed size arrays and pattern matching into switches.
module Compiler.Continuations where

import Prelude hiding (lookup)

import Utils
import Classes hiding (Context (..))

import Monad.Core (variableName)
import Monad.Typer (typeOf)
import Monad.Compiler
import Monad.Error

import Compiler.SimplSyntax
import Compiler.Circuits

import Control.Monad.Trans
import Control.Monad.Trans.Reader
import Text.PrettyPrint.HughesPJ as PP
import Data.List as List
import Data.IntMap as IntMap hiding ((\\))
import Data.IntSet as IntSet


-- | The definition of values.
data Value =
    VVar Variable              -- ^ A local variable _ function or not.
  | VInt Int                   -- ^ An integer.
  | VLabel Variable            -- ^ The label of an extern function.
  | VGlobal Variable           -- ^ A reference to a global variable.
  deriving (Show, Eq)


-- | Destruct a 'VVar' value.
getVar :: Value -> Variable
getVar (VVar x) = x
getVar _ = throwNE $ ProgramError "Instruction:getVar: illegal argument"


-- | Are considered free variables only variables bound in a local scope.
instance TermObject Value where
  freevar (VVar x) = IntSet.singleton x
  freevar _ = IntSet.empty

instance Subs Value Value where
  subs x v (VVar y) = if x == y then v else VVar y
  subs _ _ v = v


-- | Definition of continuation expressions. (divided into terminal and non terminal instructions).
data Instruction =
  -- | Function abstraction: @fun x1 .. xN -> t@. All definitions are recursive.
    Function Variable [Variable] Instruction Instruction
  -- | Application of a function, with a continuation.
  | Call Value [Value] Variable Instruction
  -- | Construction of an array: @(/t/1, .. , /t//n/)@.
  | Array [Value] Variable Instruction
  -- | Access the nth element of an array.
  | Access Int Value Variable Instruction
  -- | Switch condition (with a default target).
  | Switch Value [(Int, Instruction)] Instruction

  -- | Return a value (typically at the end of a function).
  | Ret Value
  -- | Application of a function in tail position.
  | TailCall Value [Value]
  -- | This instruction is terminal, and applicable only to global variables.
  | Set Variable Value
  -- | Throws an error message.
  | Error String
  deriving Show


instance TermObject Instruction where
  freevar (Function f args body c) =
    let functionVars = freevar body IntSet.\\ IntSet.fromList (f:args)
        cVars = IntSet.delete f $ freevar c in
    IntSet.union functionVars cVars
  freevar (Call f args x c) =
    let cVars = IntSet.delete x $ freevar c in
    IntSet.unions $ cVars:(List.map freevar (f:args))
  freevar (Array array x c) =
    let arrayVars = IntSet.unions $ List.map freevar array in
    IntSet.union (IntSet.delete x $ freevar c) arrayVars
  freevar (Access _ v x c) = IntSet.union (IntSet.delete x $ freevar c) (freevar v)
  freevar (Switch v cases def) = IntSet.unions $ List.map (freevar . snd) $ (0,def):cases
  freevar (Set x v) = freevar v -- x is ignored here because a global variable.
  freevar (Ret v) = freevar v
  freevar (TailCall f args) = IntSet.unions $ List.map freevar (f:args)
  freevar (Error _) = IntSet.empty


instance Subs Instruction Value where
  subs x v (Function f args body c) = Function f args (subs x v body) $ subs x v c
  subs x v (Call f args y c) = Call (subs x v f) (List.map (subs x v) args) y $ subs x v c
  subs x v (TailCall f args) = TailCall (subs x v f) $ List.map (subs x v) args
  subs x v (Array array y c) = Array (List.map (subs x v) array) y $ subs x v c
  subs x v (Access n w y c) = Access n (subs x v w) y $ subs x v c
  subs x v (Switch w cases def) =
    Switch (subs x v w) (List.map (\(n, c) -> (n, subs x v c)) cases) $ subs x v def
  subs x v (Set y w) = Set y $ subs x v w
  subs x v (Ret w) = Ret $ subs x v w
  subs _ _ (Error msg) = Error msg


---------------------------------------------------------------------------------------------------
-- * Compilation units.

-- | Compilation unit.
data CompilationUnit = CompilationUnit {
  imported :: [Value],          -- ^ List of functions and variables imported from extern modules.
  strings :: [Variable],        -- ^ List of constant strings used by the compile unit.
  localFunctions :: [FunctionDef],       -- ^ List of local functions.
  externFunctions :: [FunctionDef],      -- ^ List of functions accessible outside of the module.
  globalVariables :: [GlobalDef],        -- ^ Contains the list of global variables, with initializers.
  main :: Maybe Instruction     -- ^ The definition of the main function, if the module is \'Main\'.
}


-- | The type of function declarations.
type FunctionDef = (Variable, [Variable], Instruction)

-- | The type of global variable declarations.
type GlobalDef = (Variable, Instruction)


---------------------------------------------------------------------------------------------------
-- * Helpers.

-- | Fetch the value of a bound variable.
value :: Variable -> Context -> Value
value x context = do
  case IntMap.lookup x context of
    Just v -> v
    Nothing -> VVar x

-- | Valuation map.
type Context = IntMap Value

-- | Type of continuations.
type Continuation = Value -> Compiler Instruction


---------------------------------------------------------------------------------------------------
-- * CPS conversion.

-- | Conversion to CPS form (transformation from the simplified syntax to the continuation expressions
-- defined in this module).
cpsConversion :: Context -> Continuation -> Expr -> Compiler Instruction
cpsConversion ctx cont (EVar x) = do
  let v = value x ctx
  case v of
    -- global functions when handled as objects must be boxed.
    VLabel gx -> do
      closure <- createVariable "f"      -- function closure
      c <- cont $ VVar closure
      return $ Array [VLabel gx] closure c
    -- global variables when handled as objects must be unboxed.
    VGlobal gx -> do
      ref <- createVariable "ug"
      c <- cont $ VVar ref
      return $ Access 0 (VGlobal gx) ref c
    -- Normal case.
    v -> cont v

cpsConversion ctx cont (EGlobal x) = cpsConversion ctx cont $ EVar x
cpsConversion _ cont (EConstant (ConstInt n)) = cont $ VInt n
cpsConversion _ cont (EConstant (ConstBool b)) = cont $ if b then VInt 1 else VInt 0
cpsConversion _ cont (EConstant ConstUnit) = cont $ VInt 0
cpsConversion _ cont (ETuple []) = cont $ VInt 0
cpsConversion _ _ (EError msg) = return $ Error msg

cpsConversion ctx cont (ETuple tuple) = do
  x <- createVariable "x"
  c <- cont $ VVar x
  fold (\array -> return $ Array array x c) tuple []
  where
    fold cont [] array = cont $ List.reverse array
    fold cont (e:es) array = cpsConversion ctx (\v -> fold cont es (v:array)) e

cpsConversion ctx cont (EAccess n x) = do
  y <- createVariable "x"
  c <- cont $ VVar y
  let v = value x ctx
  return $ Access n v y c

cpsConversion ctx cont (EFun x e) = do
  f <- createVariable "f"       -- Function name.
  k <- createVariable "k"       -- Continuation argument.
  -- At the end of the body, the result is passed to the continuation k.
  body <- cpsConversion ctx (\z -> return $ TailCall (VVar k) [z]) e
  -- The reference f of the function is passed to the building continuation c.
  c <- cont $ VVar f
  return $ Function f [x, k] body c

cpsConversion ctx cont (EFix f x e) = do
  k <- createVariable "k"       -- Continuation argument.
  -- At the end of the body, the result is passed to the continuation k
  let ctx' = IntMap.insert f (VVar f) ctx
  body <- cpsConversion ctx' (\z -> return $ TailCall (VVar k) [z]) e
  -- The reference f of the function is passed to the building continuation c
  c <- cont $ VVar f
  return $ Function f [x, k] body c

-- The direct application of global functions is treated separately.
cpsConversion ctx cont (EApp (EVar f) arg) = do
  r <- createVariable "r"       -- Return address.
  x <- createVariable "x"       -- Argument of the return address.
  case value f ctx of
    VLabel f -> do
      c <- cpsConversion ctx (\arg ->
          return $ TailCall (VLabel f) [arg, VVar r]
        ) arg
      body <- cont $ VVar x
      return $ Function r [x] body c
    _ -> do
      -- Evaluate the argument first.
      c <- cpsConversion ctx (\f ->
          cpsConversion ctx (\arg ->
              return $ TailCall f [arg, VVar r]
            ) arg
        ) $ EVar f
      body <- cont $ VVar x
      return $ Function r [x] body c

cpsConversion ctx cont (EApp (EGlobal f) arg) =
  cpsConversion ctx cont (EApp (EVar f) arg)

cpsConversion ctx cont (EApp f arg) = do
  r <- createVariable "r"       -- Return address.
  x <- createVariable "x"       -- Argument of the return address
  c <- cpsConversion ctx (\f ->
      cpsConversion ctx (\arg ->
          return $ TailCall f [arg, VVar r]
        ) arg
    ) f
  body <- cont $ VVar x
  return $ Function r [x] body c

cpsConversion ctx cont (ESeq e f) = do
  cpsConversion ctx (\z -> cpsConversion ctx cont f) e

cpsConversion ctx cont (ELet x e f) = do
  cpsConversion ctx (\z -> do
      cpsConversion (IntMap.insert x z ctx) cont f) e

cpsConversion ctx cont (EMatch e cases def) = do
  k <- createVariable "k"
  x <- createVariable "x"
  body <- cont $ VVar x
  -- Convert the different cases.
  let cases' = List.sortBy (\(n,_) (m,_) -> compare n m) cases
  cases'' <- List.foldl (\rec (n, e) -> do
      cases <- rec
      e' <- cpsConversion ctx (\z -> return $ TailCall (VVar k) [z]) e
      return $ (n, e'):cases
    ) (return []) cases'
  -- Reduce the default case.
  def' <- cpsConversion ctx (\z -> return $ TailCall (VVar k) [z]) def
  -- Assemble.
  cpsConversion ctx (\e ->
      return $ Function k [x] body $ Switch e (List.reverse cases'') def'
    ) e


---------------------------------------------------------------------------------------------------
-- * Weak CPS conversion.

-- | Convert an expression from the simplified syntax to a weak form of the continuation passing style,
-- where only branching conditions impose the use of continuations.
wcpsConversion :: Context -> Continuation -> Expr -> Compiler Instruction
wcpsConversion ctx cont (EVar x) =
  case value x ctx of
    -- Global functions when handled as objects must be boxed.
    VLabel gx -> do
      closure <- createVariable "f"      -- function closure
      c <- cont $ VVar closure
      return $ Array [VLabel gx] closure c
    -- Global variables when handled as objects must be unboxed.
    VGlobal gx -> do
      ug <- createVariable "ug"
      c <- cont $ VVar ug
      return $ Access 0 (VGlobal gx) ug c
    -- Normal case.
    v -> cont v

wcpsConversion ctx cont (EGlobal x) = wcpsConversion ctx cont $ EVar x
wcpsConversion _ cont (EConstant (ConstInt n)) = cont $ VInt n
wcpsConversion _ cont (EConstant (ConstBool b)) = cont $ if b then VInt 1 else VInt 0
wcpsConversion _ cont (EConstant ConstUnit) = cont $ VInt 0
wcpsConversion _ cont (ETuple []) = cont $ VInt 0
wcpsConversion _ _ (EError msg) = return $ Error msg

wcpsConversion ctx cont (ETuple tuple) = do
  x <- createVariable "x"
  c <- cont $ VVar x
  fold (\array -> return $ Array array x c) tuple []
  where
    fold cont [] array = cont $ List.reverse array
    fold cont (e:es) array = wcpsConversion ctx (\v -> fold cont es (v:array)) e

wcpsConversion ctx cont (EAccess n x) = do
  y <- createVariable "x"
  c <- cont $ VVar y
  return $ Access n (value x ctx) y c

wcpsConversion ctx cont (EFun x e) = do
  f <- createVariable "f"       -- Function name.
  -- At the end of the body, the result is returned using Ret.
  body <- wcpsConversion ctx (\z -> return $ Ret z) e
  -- The reference f of the function is passed to the building continuation c.
  c <- cont $ VVar f
  return $ Function f [x] body c

wcpsConversion ctx cont (EFix f x e) = do
  -- At the end of the body, the result is returned using Ret.
  let ctx' = IntMap.insert f (VVar f) ctx
  body <- wcpsConversion ctx' (\z -> return $ Ret z) e
  -- The reference f of the function is passed to the building continuation c.
  c <- cont $ VVar f
  return $ Function f [x] body c

-- The direct application of global functions is treated separately.
wcpsConversion ctx cont (EApp (EVar f) arg) = do
  x <- createVariable "x"    -- Result of the application.
  case value f ctx of
    VLabel f -> do
      c <- cont $ VVar x
      wcpsConversion ctx (\arg ->
          return $ Call (VLabel f) [arg] x c) arg
    _ -> do
      c <- cont $ VVar x
      wcpsConversion ctx (\f ->
          wcpsConversion ctx (\arg ->
              return $ Call f [arg] x c
            ) arg
        ) $ EVar f

wcpsConversion ctx cont (EApp (EGlobal f) arg) =
  wcpsConversion ctx cont $ EApp (EVar f) arg

wcpsConversion ctx cont (EApp f arg) = do
  x <- createVariable "x"       -- Result of the application.
  c <- cont $ VVar x
  wcpsConversion ctx (\f ->
      wcpsConversion ctx (\arg ->
          return $ Call f [arg] x c
        ) arg
    ) f

wcpsConversion ctx cont (ESeq e f) = do
  wcpsConversion ctx (\z -> wcpsConversion ctx cont f) e

wcpsConversion ctx cont (ELet x e f) = do
  wcpsConversion ctx (\z -> do
      wcpsConversion (IntMap.insert x z ctx) cont f) e

wcpsConversion ctx cont (EMatch e cases def) = do
  k <- createVariable "k"
  x <- createVariable "x"
  body <- cont $ VVar x
  -- Convert the different cases.
  let cases' = List.sortBy (\(n,_) (m,_) -> compare n m) cases
  cases'' <- List.foldl (\rec (n, e) -> do
      cases <- rec
      e' <- wcpsConversion ctx (\z -> return $ TailCall (VVar k) [z]) e
      return $ (n, e'):cases
    ) (return []) cases'
  -- Reduce the default case.
  def' <- wcpsConversion ctx (\z -> return $ TailCall (VVar k) [z]) def
  -- Assemble.
  wcpsConversion ctx (\e ->
      return $ Function k [x] body $ Switch e (List.reverse cases'') def'
    ) e


---------------------------------------------------------------------------------------------------
-- * Program statistics.

-- | Usage information : number of uses and escapes.
data Usage = Usage { uses :: Int, escapes :: Int }

-- | Describe for each kind of bound variable the information
-- needed for the optimizations.
data Information =
    IFun [Variable] Instruction
  | ITuple [Value]
  | IAccess Variable Int
  | IParam
  | ICall
  | IOther


-- | No usage.
noUsage :: Usage
noUsage = Usage { uses = 0, escapes = 0 }

-- | Update the information regarding a variable.
updateUsage :: ((Usage, Information) -> Maybe (Usage, Information))
  -> IntMap (Usage, Information) -> Value
  -> IntMap (Usage, Information)
updateUsage f info (VVar x) = IntMap.update f x info
updateUsage f info (VLabel x) = IntMap.update f x info
updateUsage f info (VGlobal x) = IntMap.update f x info
updateUsage _ info _ = info

-- | Increase the number of uses of a variable.
increaseUses :: IntMap (Usage, Information) -> Value -> IntMap (Usage, Information)
increaseUses = updateUsage (\(usage, info) -> Just (usage { uses = uses usage + 1 }, info))

-- | Increase the number of uses of a variable.
increaseEscapes :: IntMap (Usage, Information) -> Value -> IntMap (Usage, Information)
increaseEscapes = updateUsage (\(usage, info) -> Just (usage { escapes = escapes usage + 1 }, info))

-- | Lookup the information about a value.
lookupUsage :: Value -> IntMap (Usage, Information) -> Maybe (Usage, Information)
lookupUsage (VVar x) info = IntMap.lookup x info
lookupUsage (VLabel x) info = IntMap.lookup x info
lookupUsage (VGlobal x) info = IntMap.lookup x info
lookupUsage _ _ = Nothing

-- | Do a pass to gather information. The usage is particularly important as knowing it can enable
-- closure optimizations.
computeUsage :: IntMap (Usage, Information) -> Instruction -> IntMap (Usage, Information)
computeUsage info (Function g arg body c) =
  let info' = List.foldl (\info a ->
          IntMap.insert a (noUsage, IParam) info
        ) (IntMap.insert g (noUsage, IFun arg body) info) arg in
  computeUsage (computeUsage info' body) c
computeUsage info (TailCall f arg) =
  List.foldl increaseEscapes (increaseUses info f) arg
computeUsage info (Call f arg x c) =
  let info' = List.foldl increaseEscapes (increaseUses info f) arg in
  computeUsage (IntMap.insert x (noUsage, ICall) info') c
computeUsage info (Array vals x c) =
  let info' = List.foldl increaseEscapes info vals in
  computeUsage (IntMap.insert x (noUsage, ITuple vals) info') c
computeUsage info (Access n v x c) =
  let info' = increaseUses info v in
  computeUsage (IntMap.insert x (noUsage, IAccess (getVar v) n) info') c
computeUsage info (Switch v clist c) =
  let info' = increaseUses info v in
  List.foldl (\info (_,c) -> computeUsage info c) (computeUsage info' c) clist
computeUsage info (Ret v) =
  increaseEscapes info v
computeUsage info (Set x v) =
  -- Since [x] here is supposed to be a global variable, no need
  -- to track it down.
  increaseEscapes info v
computeUsage info (Error msg) =
  info


---------------------------------------------------------------------------------------------------
-- * Closure conversion.

-- | Closure conversion of the CPS code. This auxiliary function also returns the set of free
-- variables of the produced expression. The goal of this transformation is to remove all the free
-- variables of a function. Optimally, all the free variables could be passed as addtional arguments,
-- but this is not always possible (when the function escapes the scope by being returned by a function).
-- The rest of the time, a closure (local environment) is built and passed as argument.
closureConversion :: IntMap (Usage, Information) -> Instruction -> Compiler (Instruction, IntSet)
closureConversion info (Function f args body c) = do
  -- Check the usage of the function [f].
  case IntMap.lookup f info of
    -- The function doesn't need to be closed. Instead, the free variables are passed as arguments.
    Just (usage @ Usage { escapes = 0 } , _) -> do
      let envf = freevar body IntSet.\\ (IntSet.fromList (f:args))
      let closure = IntSet.toList envf
      -- Update the information about [f] to convey the free variables.
      let info' = IntMap.insert f (usage, IFun closure body) info
      (body', _) <- closureConversion info' body
      (c', envc) <- closureConversion info' c
      return (Function f (args ++ closure) body' c', IntSet.union envf $ IntSet.delete f envc)
    -- Generate a function closure, and the instructions to access the variables in the context.
    _ -> do
      (body', envf) <- closureConversion info body
      (c', envc) <- closureConversion info c
      let envf' = envf IntSet.\\ IntSet.fromList (f:args)
      let closure = IntSet.toList envf'
      -- Extraction of the closure's variables (code added at the beginning of the function block).
      -- The closure argument has the same name as the function (variable f here).
      let (_, body'') = List.foldl (\(n, body) x ->
            (n+1, Access n (VVar f) x body)) (0, body') closure
      -- Construction of the closure (with continuation c' and name f).
      let c'' = Array (VVar f:(List.map VVar closure)) f c'
      -- Re-definition of the function f.
      return (Function f (f:args) body'' c'', IntSet.union envf' $ IntSet.delete f envc)

closureConversion info (Call (VVar f) args x c) = do
  -- Check the usage of the function [f].
  case IntMap.lookup f info of
    -- The function is known: no closure argument, instead
    -- the free variables added to the list of arguments.
    Just (Usage { escapes = 0 }, IFun closure _) -> do
      (c', envc) <- closureConversion info c
      let envl = IntSet.insert f $ IntSet.unions $ (IntSet.fromList closure):(List.map freevar args)
      let env = IntSet.union (IntSet.delete x envc) envl
      return (Call (VVar f) (args ++ List.map VVar closure) x c', env)
    -- Not this luck, the function must first be extracted from the closure, before being called.
    -- The function is the first element of the closure.
    _ -> do
      (c', envc) <- closureConversion info c
      f' <- createVariable "f"
      let envl = IntSet.insert f $ IntSet.unions $ List.map freevar args
      let env = IntSet.union (IntSet.delete x envc) envl
      return ( Access 0 (VVar f) f' $ Call (VVar f') (VVar f:args) x c', env)

-- Since global functions are already closed, only a dummy closure is passed as argument.
closureConversion info (Call (VLabel f) args x c) = do
  (c', envc) <- closureConversion info c
  let env = IntSet.union (IntSet.delete x envc) $ IntSet.unions $ List.map freevar args
  return ( Call (VLabel f) (VInt 0:args) x c', env)

-- Da capo.
closureConversion info (TailCall (VVar f) args) = do
  -- Check the usage of the function [f].
  case IntMap.lookup f info of
    -- The function is known: no closure argument, instead
    -- the free variables added to the list of arguments.
    Just (Usage { escapes = 0 }, IFun closure _) -> do
      let env = IntSet.insert f $ IntSet.unions $ (IntSet.fromList closure):(List.map freevar args)
      return (TailCall (VVar f) (args ++ List.map VVar closure), env)
    -- Not this luck, the function must first be extracted from the closure, before being called.
    -- The function is the first element of the closure.
    _ -> do
      f' <- createVariable "f"
      let env = IntSet.insert f $ IntSet.unions $ List.map freevar args
      return ( Access 0 (VVar f) f' $ TailCall (VVar f') (VVar f:args), env)

-- Since global functions are already closed, only a dummy closure is passed as argument.
closureConversion info (TailCall (VLabel f) args) = do
  return ( TailCall (VLabel f) (VInt 0:args), IntSet.unions $ List.map freevar args )

-- Recursive call.
closureConversion info (Array array x c) = do
  (c', envc) <- closureConversion info c
  let enva = IntSet.unions $ List.map freevar array
  return (Array array x c', IntSet.union enva $ IntSet.delete x envc)

closureConversion info (Access n v x c) = do
  (c', envc) <- closureConversion info c
  return (Access n v x c', IntSet.union (freevar v) (IntSet.delete x envc))

closureConversion info (Switch v cases def) = do
  (cases', envc) <- List.foldl (\rec (n, c) -> do
      (cases, envc) <- rec
      (c', envc') <- closureConversion info c
      return ((n, c'):cases, IntSet.union envc' envc)
    ) (return ([], IntSet.empty)) cases
  (def', envd) <- closureConversion info def
  return (Switch v (List.reverse cases') def', IntSet.unions [freevar v, envc, envd])

closureConversion _ e = return (e, freevar e)


-- | Closure conversion of the CPS code.
closure_conversion :: Instruction -> Compiler Instruction
closure_conversion e = do
  (e, _) <- closureConversion (computeUsage IntMap.empty e) e
  return e


---------------------------------------------------------------------------------------------------
-- * Module transformations.

-- | Convert the toplevel declarations into CPS form.
convert_declarations_to_cps :: [Declaration]            -- ^ List of declarations.
                            -> Compiler CompilationUnit              -- ^ Resulting compile unit.
convert_declarations_to_cps decls = do
  -- build the list of imported variables
  let imports = List.foldl (\imp (DLet _ _ e) -> List.union (imported e) imp) [] decls
  (ivals, imported) <- List.foldl (\rec ix -> do
        (ivals, imported) <- rec
        tix <- runTyper $ typeOf ix
        if isFunction tix then
          return (IntMap.insert ix (VLabel ix) ivals, (VLabel ix):imported)
        else
          return (IntMap.insert ix (VGlobal ix) ivals, (VGlobal ix):imported)) (return (IntMap.empty, [])) imported

  -- translate the declarations
  (cu, _) <- List.foldl (\rec (DLet vis f e) -> do
        (cu, vals) <- rec
        n <- runCore $ variableName f
        -- TODO XXX Check the type of the main function.
        case (n,e) of
          ("main", EFun _ c) -> do
              body <- cpsConversion vals (\z -> return $ Ret z) c
              body <- return $ constant_folding 3 body
              (funs, body) <- closure_conversion body >>= return . lift_functions
              return (cu { main = Just body, local = funs ++ local cu }, vals)

          (_, EFun x c) -> do
              k <- createVariable "k"       -- continuation argument
              fc <- createVariable "fc"     -- closure argument
              body <- cpsConversion vals (\z -> return $ TailCall (VVar k) [z]) c
              body <- return $ constant_folding 3 body
              (funs, body) <- closure_conversion body >>= return . lift_functions
              let fdef = (f, [fc,x,k], body)
              case vis of
                Internal ->
                    return (cu { local = funs ++ [fdef] ++ local cu }, IntMap.insert f (VLabel f) vals)
                External ->
                    return (cu { local = funs ++ local cu, externFunctions = fdef:(externFunctions cu) }, IntMap.insert f (VLabel f) vals)

          (_, EFix _ x c) -> do
              k <- createVariable "k"       -- continuation argument
              fc <- createVariable "fc"     -- closure argument
              let vals' = IntMap.insert f (VLabel f) vals
              body <- cpsConversion vals' (\z -> return $ TailCall (VVar k) [z]) c
              body <- return $ constant_folding 3 body
              (funs, body) <- closure_conversion body >>= return . lift_functions
              let fdef = (f, [fc,x,k], body)
              case vis of
                Internal ->
                    return (cu { local = funs ++ [fdef] ++ local cu }, vals')
                External ->
                    return (cu { local = funs ++ local cu, externFunctions = fdef:(externFunctions cu) }, vals')

          _ -> do
              -- translate the computation of g
              init <- cpsConversion vals (\z -> return $ Set f z) e
              (funs,init) <- closure_conversion init >>= return . lift_functions
              -- return the extend compile unit
              return (cu { local = funs ++ local cu, globalVariables = (f, init):(globalVariables cu) }, IntMap.insert f (VGlobal f) vals)

    ) (return (CompilationUnit { local = [], externFunctions = [], globalVariables = [], imported = imported, strings = [], main = Nothing }, ivals)) decls
  return cu { externFunctions = List.reverse $ externFunctions cu, globalVariables = List.reverse $ globalVariables cu }


-- | Convert the toplevel declarations into wCPS form.
convert_declarations_to_wcps :: [Declaration]            -- ^ List of declarations.
                             -> Compiler CompilationUnit              -- ^ Resulting compile unit.
convert_declarations_to_wcps decls = do
  -- build the list of imported variables
  let imported = List.foldl (\imp (DLet _ _ e) -> List.union (imported e) imp) [] decls
  (ivals, imported) <- List.foldl (\rec ix -> do
        (ivals, imported) <- rec
        tix <- runTyper $ typeOf ix
        if isFunction tix then
          return (IntMap.insert ix (VLabel ix) ivals, (VLabel ix):imported)
        else
          return (IntMap.insert ix (VGlobal ix) ivals, (VGlobal ix):imported)) (return (IntMap.empty, [])) imported

  -- translate the declarations
  (cu, _) <- List.foldl (\rec (DLet vis f e) -> do
        (cu, vals) <- rec
        n <-  runCore $ variableName f
        case (n, e) of
          ("main", EFun _ c) -> do
              body <- wcpsConversion vals (\z -> return $ Ret z) c
              body <- return $ constant_folding 3 body
              (funs, body) <- closure_conversion body >>= return . lift_functions
              return (cu { main = Just body, local = funs ++ local cu }, vals)

          (_, EFun x c) -> do
              fc <- createVariable "fc"     -- closure argument
              body <- wcpsConversion vals (\z -> return $ Ret z) c
              body <- return $ constant_folding 3 body
              (funs, body) <- closure_conversion body >>= return . lift_functions
              let fdef = (f, [fc,x], body)
              case vis of
                Internal ->
                    return (cu { local = funs ++ [fdef] ++ local cu },
                            IntMap.insert f (VLabel f) vals)
                External ->
                    return (cu { local = funs ++ local cu, externFunctions = fdef:(externFunctions cu) },
                            IntMap.insert f (VLabel f) vals)

          (_, EFix _ x c) -> do
              fc <- createVariable "fc"     -- closure argument
              let vals' = IntMap.insert f (VLabel f) vals
              body <- wcpsConversion vals' (\z -> return $ Ret z) c
              body <- return $ constant_folding 3 body
              (funs, body) <- closure_conversion body >>= return . lift_functions
              let fdef = (f, [fc,x], body)
              case vis of
                Internal ->
                    return (cu { local = funs ++ [fdef] ++ local cu }, vals')
                External ->
                    return (cu { local = funs ++ local cu, externFunctions = fdef:(externFunctions cu) }, vals')

          _ -> do
              -- translate the computation of g
              init <- wcpsConversion vals (\z -> return $ Set f z) e
              (funs,init) <- closure_conversion init >>= return . lift_functions
              -- return the extend compile unit
              return (cu { local = funs ++ local cu, globalVariables = (f, init):(globalVariables cu) }, IntMap.insert f (VGlobal f) vals)

    ) (return (CompilationUnit { local = [], externFunctions = [], globalVariables = [], imported = imported, strings = [], main = Nothing }, ivals)) decls
  return cu { externFunctions = List.reverse $ externFunctions cu, globalVariables = List.reverse $ globalVariables cu }





-- | Lift the function definitions to the top of the module.
-- This function separates the function definitions from the rest of the continuation expression.
-- Since this operation is sound only if the functions are closed, this has to be done after the closure conversion.
lift_functions :: Instruction -> ([FunctionDef], Instruction)
lift_functions (Function f args cf c) =
  let (funs, c') = lift_functions c
      (funs', cf') = lift_functions cf in
  ((f,args,cf'):(funs' ++ funs), c')

lift_functions (Array vlist x c) =
  let (funs, c') = lift_functions c in
  (funs, Array vlist x c')

lift_functions (Access n x y c) =
  let (funs, c') = lift_functions c in
  (funs, Access n x y c')

lift_functions (Switch v clist def) =
  let (funs, clist') = List.foldl (\(fs, cl) (n,c) ->
        let (fs', c') = lift_functions c in
        (fs' ++ fs, (n,c'):cl)) ([], []) clist
      (funs', def') = lift_functions def in

  (funs ++ funs', Switch v (List.reverse clist') def')

lift_functions (Call f args x c) =
  let (funs, c') = lift_functions c in
  (funs, Call f args x c')

lift_functions c =
 ([], c)



-- | Check a value.
check_value :: [Variable] -> Value -> Compiler ()
check_value scope (VVar v) =
  if List.elem v scope then return ()
  else do
    n <-  runCore $ variableName v
    fail $ "Instruction:check_value: undefined variable " ++ n
check_value scope _ =
  return ()


-- * This section is dedicated to code optimization.


-- | Perform a certain number of optimization passes of constant folding.
-- These include:
--
-- * If a function is non-escaping, then it can be closed by passing the free variables
-- additional as arguments.
--
-- * If a function is non-escaping and used only once, then it can be inlined.
--
-- * If an access is made on a tuple that is known at compile time, it can
-- be replaced by its known value.
--
-- * Dead variable elimination.
constant_folding :: Int -> Instruction -> Instruction
constant_folding n c =
  if not ((n > 0) && (n < 5)) then
    throwNE $ ProgramError "Instruction:constant_folding: illegal number of iterations"
  else
    let opt info (Function f arg body c) =
          -- Optimize the body.
          let body' = opt info body in
          Function f arg body' (opt info c)
        opt info (TailCall f vals) =
          TailCall f vals
        opt info (Call f vals x c) =
          Call f vals x $ opt info c
        opt info (Array vals x c) =
          case IntMap.lookup x info of
            Just (usage, inf) ->
                -- If the tuple is not used, remove it.
                if uses usage + escapes usage == 0 then
                  opt info c
                else Array vals x $ opt info c
            Nothing -> Array vals x $ opt info c
        opt info (Access n v x c) =
          case IntMap.lookup x info of
            Just (usage, inf) ->
                -- If the tuple is not used, remove it.
                if uses usage + escapes usage == 0 then
                  opt info c
                else
                  case lookupUsage v info of
                    Just (_, ITuple vals) ->
                        -- In case the value being accessed is a tuple,
                        -- replace [x] by its known value.
                        opt info $ subs x (vals !! n) c
                    _ ->
                        Access n v x $ opt info c
            _ -> Access n v x $ opt info c
        opt info (Switch (VInt n) clist def) =
          -- If the value by compared is known at compile time,
          -- just access the expected branch.
          case List.lookup n clist of
            Just c -> opt info c
            Nothing -> opt info def
        opt info (Switch v clist def) =
          Switch v (List.map (\(n,c) -> (n, opt info c)) clist) $ opt info def
        opt info c = c
    in
    List.foldl (\c n ->
      opt (computeUsage IntMap.empty c) c) c [1..n]



-- | Check the scope of the variables of the continuation expression.
check_cexpr :: [Variable] -> Instruction -> Compiler ()
check_cexpr scope (Function g arg body c) = do
  let nscope = List.union scope arg
  check_cexpr nscope body
  check_cexpr (g:scope) c
check_cexpr scope (TailCall f arg) = do
  check_value scope f
  List.foldl (\rec a -> do
        rec
        check_value scope a) (return ()) arg
check_cexpr scope (Call f arg x c) = do
  check_value scope f
  List.foldl (\rec a -> do
        rec
        check_value scope a) (return ()) arg
  check_cexpr (x:scope) c
check_cexpr scope (Array vals x c) = do
  List.foldl (\rec v -> do
        rec
        check_value scope v) (return ()) vals
  check_cexpr (x:scope) c
check_cexpr scope (Access n v x c) = do
  check_value scope v
  check_cexpr (x:scope) c
check_cexpr scope (Switch v clist c) = do
  check_value scope v
  List.foldl (\rec (_,c) -> do
        rec
        check_cexpr scope c) (return ()) clist
  check_cexpr scope c
check_cexpr scope (Ret v) =
  check_value scope v
check_cexpr scope (Set x v) =
  check_value scope v
check_cexpr scope (Error msg) =
  return ()


-- | Check the scope of the variables of a compile unit.
check_cunit :: CompilationUnit -> Compiler ()
check_cunit cu = do
  let scope = List.map (\(f,_,_) -> f) (local cu) ++ List.map (\(f,_,_) -> f) (externFunctions cu) ++ List.map fst (globalVariables cu)
  List.foldl (\rec (_, arg, c) -> do
        rec
        check_cexpr (List.union arg scope) c) (return ()) (local cu ++ externFunctions cu)
  case main cu of
    Just c -> check_cexpr scope c
    Nothing -> return ()

-- | Pretty-print a value using Hughes's and Peyton Jones's
-- pretty printer combinators. The type 'Doc' is defined in the library
-- "Text.PrettyPrint.HughesPJ" and allows for nested documents.
print_value :: (Variable -> String)  -- ^ Rendering of term variables.
            -> Value                 -- ^ Instruction to print.
            -> Doc                   -- ^ Resulting PP document.
print_value _ (VInt n) =
  text (show n)
print_value fvar (VVar v) =
  text (fvar v)
print_value fvar (VGlobal v) =
  text (fvar v)
print_value fvar (VLabel v) =
  text (fvar v)

-- | Pretty-print an expression using Hughes's and Peyton Jones's
-- pretty printer combinators. The type 'Doc' is defined in the library
-- "Text.PrettyPrint.HughesPJ" and allows for nested documents.
print_cfun :: (Variable -> String)                      -- ^ Rendering of term variables.
           -> (Variable, [Variable], Instruction)             -- ^ Function to print.
           -> Doc                                       -- ^ Resulting PP document.
print_cfun fvar (f, [], cf) =
  text (fvar f ++ "() {") $$
  nest 2 (print_cexpr Inf fvar cf) $$
  text "}"
print_cfun fvar (f, args, cf) =
  let pargs = List.map (text . fvar) args
      sargs = punctuate comma pargs in
  text (fvar f ++ "(") <> hsep sargs <> text ") {" $$
  nest 2 (print_cexpr Inf fvar cf) $$
  text "}"


-- | Pretty-print a continuation function using Hughes's and Peyton Jones's
-- pretty printer combinators. The type 'Doc' is defined in the library
-- "Text.PrettyPrint.HughesPJ" and allows for nested documents.
print_cexpr :: Lvl                   -- ^ Maximum depth.
            -> (Variable -> String)  -- ^ Rendering of term variables.
            -> Instruction                 -- ^ Instruction to print.
            -> Doc                   -- ^ Resulting PP document.
print_cexpr _ fvar (Call f args x c) =
  let pargs = List.map (print_value fvar) args
      sargs = punctuate comma pargs in
  text (fvar x) <+> text ":=" <+> print_value fvar f <> text "(" <> hsep sargs <> text ");" $$
  print_cexpr Inf fvar c
print_cexpr _ fvar (TailCall f args) =
  let pargs = List.map (print_value fvar) args
      sargs = punctuate comma pargs in
  print_value fvar f <> text "(" <> hsep sargs <> text ");"
print_cexpr _ fvar (Array vals x c) =
  let pvals = List.map (print_value fvar) vals
      svals = punctuate comma pvals in
  text (fvar x ++ " := [") <> hsep svals <> text "];" $$
  print_cexpr Inf fvar c
print_cexpr _ fvar (Access n x y c) =
  text (fvar y ++ " :=") <+> print_value fvar x <> text ("[" ++ show n ++ "];") $$
  print_cexpr Inf fvar c
print_cexpr _ fvar (Switch v clist def) =
  let pcs = List.map (\(n,c) -> (n,print_cexpr Inf fvar c)) clist
      pdef = text "default:" $$ nest 2 (print_cexpr Inf fvar def) in
  text "switch" <+> print_value fvar v <+> text "with" $$
  nest 2 (List.foldl (\doc (tag, c) ->
        doc $$
        text (show tag ++ ":") $$
        nest 2 c) PP.empty pcs $$ pdef)
print_cexpr _ fvar (Function f arg cf c) =
  print_cfun fvar (f, arg, cf) $$
  print_cexpr Inf fvar c
print_cexpr _ fvar (Set x v) =
  text (fvar x) <+> text ":=" <+> print_value fvar v
print_cexpr _ fvar (Ret v) =
  text "ret" <+> print_value fvar v
print_cexpr _ fvar (Error msg) =
  text "error \"" <> text msg <> text "\""


instance PPrint Instruction where
  -- Generic printing
  genprint lv [fvar] e =
    let doc = print_cexpr lv fvar e in
    PP.render doc
  genprint lv _ e =
    throwNE $ ProgramError "CPS:genprint(Instruction): illegal argument"

  -- Other
  -- By default, the term variables are printed as x_n and the data constructors as D_n,
  -- where n is the id of the variable / constructor
  sprintn lv e = genprint lv [prevar "%"] e



instance PPrint CompilationUnit where
  genprint _ [fvar] cu =
    let pcfuns = List.map (print_cfun fvar) (externFunctions cu ++ local cu) in
    let (gdef, ginit) = List.unzip $ List.map (\(g, e) ->
          (text (fvar g), print_cexpr Inf fvar e)) (globalVariables cu) in
    let pimport = List.map (\v -> case v of
          VLabel x -> text $ fvar x
          VGlobal x -> text $ fvar x
          _ -> text "WATWATWAT") (imported cu) in
    let pmain = case main cu of
          Just m -> text "main () {" $$ nest 2 (print_cexpr Inf fvar m) $$ text "}" $$ text " "
          Nothing -> text " " in

    let all =
          text "extern" <+> hsep (punctuate comma pimport) $$
          text "globals" <+> hsep (punctuate comma gdef) $$ text " " $$
          text "init () {" $$ nest 2 (vcat ginit) $$ text "}" $$ text " " $$
          pmain $$
          vcat pcfuns in
    PP.render all
  genprint _ _ _ =
    throwNE $ ProgramError "CPS:genprint(CompilationUnit): illegal argument"

  sprintn lv e = genprint lv [prevar "%"] e
