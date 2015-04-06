{-# LANGUAGE MultiParamTypeClasses #-}

-- | This module contains the definition of the last language used before the construction of the
-- LLVM module. It explicitates the flow control, under the form of continuation expressions. Language
-- operators are close to those used in LLVM-IR. In particular, data constructors are explicitated into
-- fixed size arrays and pattern matching into switches.
module Compiler.Continuations where

import Prelude hiding (lookup)

import Utils
import Classes hiding (Context (..))
import Options (conversionFormat)

import Monad.Core (variableName, getOptions)
import Monad.Typer (typeOf)
import Monad.Compiler
import Monad.Error

import Compiler.SimplSyntax as SimplSyntax
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
  imports :: [Value],           -- ^ List of functions and variables imported from extern modules.
  strings :: [Variable],        -- ^ List of constant strings used by the compile unit.
  localFunctions :: [FunctionDef],       -- ^ List of local functions.
  externFunctions :: [FunctionDef],      -- ^ List of functions accessible outside of the module.
  globalVariables :: [GlobalDef],        -- ^ Contains the list of global variables, with initializers.
  main :: Maybe Instruction     -- ^ The definition of the main function, if the module is \'Main\'.
}


-- | Create a new compilation unit initialized with imported variables.
createUnit :: [Value] -> CompilationUnit
createUnit imports =
  CompilationUnit {
      localFunctions = [],
      externFunctions = [],
      globalVariables = [],
      imports = imports,
      strings = [],
      main = Nothing
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
convertDeclarationsToCps :: [Declaration]             -- ^ List of declarations.
                        -> Compiler CompilationUnit  -- ^ Resulting compilation unit.
convertDeclarationsToCps decls = do
  -- Build the list of imported variables.
  let imported = List.foldl (\imp (DLet _ _ e) -> List.union (SimplSyntax.imported e) imp) [] decls
  -- Build the intial context of the transformation.
  (context, imported) <- List.foldl (\rec x -> do
      (context, imported) <- rec
      typ <- runTyper $ typeOf x
      if isFunction typ then return (IntMap.insert x (VLabel x) context, (VLabel x):imported)
      else return (IntMap.insert x (VGlobal x) context, (VGlobal x):imported)
    ) (return (IntMap.empty, [])) imported

  -- Translate the declarations.
  (unit, _) <- List.foldl (\rec (DLet visibility f e) -> do
      (unit, context) <- rec
      name <- runCore $ variableName f
      -- TODO XXX Check the type of the main function.
      case (name, e) of
        ("main", EFun _ body) -> do
          body <- cpsConversion context (\z -> return $ Ret z) body
          body <- return $ constant_folding 3 body
          (funs, body) <- closure_conversion body >>= return . liftFunctions
          return (unit {
              main = Just body,
              localFunctions = funs ++ localFunctions unit
            }, context)

        (_, EFun x body) -> do
            k <- createVariable "k"       -- Continuation argument.
            fc <- createVariable "fc"     -- Closure argument.
            body <- cpsConversion context (\z -> return $ TailCall (VVar k) [z]) body
            body <- return $ constant_folding 3 body
            (funs, body) <- closure_conversion body >>= return . liftFunctions
            let fdef = (f, [fc,x,k], body)
            case visibility of
              Internal ->
                return (unit {
                    localFunctions = funs ++ [fdef] ++ localFunctions unit
                  }, IntMap.insert f (VLabel f) context)
              External ->
                return (unit {
                    localFunctions = funs ++ localFunctions unit,
                    externFunctions = fdef:(externFunctions unit)
                  }, IntMap.insert f (VLabel f) context)

        (_, EFix _ x body) -> do
            k <- createVariable "k"       -- Continuation argument.
            fc <- createVariable "fc"     -- Closure argument.
            let context' = IntMap.insert f (VLabel f) context
            body <- cpsConversion context' (\z -> return $ TailCall (VVar k) [z]) body
            body <- return $ constant_folding 3 body
            (funs, body) <- closure_conversion body >>= return . liftFunctions
            let fdef = (f, [fc,x,k], body)
            case visibility of
              Internal ->
                return (unit { localFunctions = funs ++ [fdef] ++ localFunctions unit }, context')
              External ->
                return (unit {
                    localFunctions = funs ++ localFunctions unit,
                    externFunctions = fdef:(externFunctions unit)
                  }, context')
        _ -> do
            -- Translate the computation of the global variable g (initializer).
            init <- cpsConversion context (\z -> return $ Set f z) e
            (funs, init) <- closure_conversion init >>= return . liftFunctions
            -- Return the extended compilation unit.
            return (unit {
                localFunctions = funs ++ localFunctions unit,
                globalVariables = (f, init):(globalVariables unit)
              }, IntMap.insert f (VGlobal f) context)

    ) (return (createUnit imported, context)) decls
  -- Reorganize the declarations and return the compilation unit.
  return unit {
      externFunctions = List.reverse $ externFunctions unit,
      globalVariables = List.reverse $ globalVariables unit
    }


-- | Convert the toplevel declarations into wCPS form.
convertDeclarationsToWcps :: [Declaration]            -- ^ List of declarations.
                          -> Compiler CompilationUnit              -- ^ Resulting compile unit.
convertDeclarationsToWcps decls = do
  -- Build the list of imported variables.
  let imported = List.foldl (\imp (DLet _ _ e) -> List.union (SimplSyntax.imported e) imp) [] decls
  -- Build the intial context of the transformation.
  (context, imported) <- List.foldl (\rec x -> do
      (context, imported) <- rec
      typ <- runTyper $ typeOf x
      if isFunction typ then return (IntMap.insert x (VLabel x) context, (VLabel x):imported)
      else return (IntMap.insert x (VGlobal x) context, (VGlobal x):imported)
    ) (return (IntMap.empty, [])) imported

  -- Translate the declarations.
  (unit, _) <- List.foldl (\rec (DLet visibility f e) -> do
      (unit, context) <- rec
      name <-  runCore $ variableName f
      case (name, e) of
        ("main", EFun _ body) -> do
          body <- wcpsConversion context (\z -> return $ Ret z) body
          body <- return $ constant_folding 3 body
          (funs, body) <- closure_conversion body >>= return . liftFunctions
          return (unit {
              main = Just body,
              localFunctions = funs ++ localFunctions unit
            }, context)

        (_, EFun x body) -> do
            fc <- createVariable "fc"     -- Closure argument.
            body <- wcpsConversion context (\z -> return $ Ret z) body
            body <- return $ constant_folding 3 body
            (funs, body) <- closure_conversion body >>= return . liftFunctions
            let fdef = (f, [fc,x], body)
            case visibility of
              Internal ->
                return (unit {
                    localFunctions = funs ++ [fdef] ++ localFunctions unit
                  }, IntMap.insert f (VLabel f) context)
              External ->
                return (unit {
                    localFunctions = funs ++ localFunctions unit,
                    externFunctions = fdef:(externFunctions unit)
                  }, IntMap.insert f (VLabel f) context)

        (_, EFix _ x body) -> do
            fc <- createVariable "fc"     -- closure argument
            let context' = IntMap.insert f (VLabel f) context
            body <- wcpsConversion context' (\z -> return $ Ret z) body
            body <- return $ constant_folding 3 body
            (funs, body) <- closure_conversion body >>= return . liftFunctions
            let fdef = (f, [fc,x], body)
            case visibility of
              Internal ->
                return (unit { localFunctions = funs ++ [fdef] ++ localFunctions unit }, context')
              External ->
                return (unit {
                    localFunctions = funs ++ localFunctions unit,
                    externFunctions = fdef:(externFunctions unit)
                  }, context')

        _ -> do
          -- Translate the computation of the global variable g.
          init <- wcpsConversion context (\z -> return $ Set f z) e
          (funs, init) <- closure_conversion init >>= return . liftFunctions
          -- Return the extended compilation unit.
          return (unit {
              localFunctions = funs ++ localFunctions unit,
              globalVariables = (f, init):(globalVariables unit)
            }, IntMap.insert f (VGlobal f) context)

    ) (return (createUnit imported, context)) decls
  -- Reorganize the declarations and return the compilation unit.
  return unit {
      externFunctions = List.reverse $ externFunctions unit,
      globalVariables = List.reverse $ globalVariables unit
    }


-- | Convert the declarations, selecting the format from the core options.
convertDeclarations :: [Declaration] -> Compiler CompilationUnit
convertDeclarations declarations = do
  options <- runCore getOptions
  case conversionFormat options of
    "cps" -> convertDeclarationsToCps declarations
    "wcps" -> convertDeclarationsToWcps declarations
    _ -> fail "Continuations.convertDeclarations: illegal format"


-- | Lift the function definitions to the top of the module.
-- This function separates the function definitions from the rest of the continuation expression.
-- Since this operation is sound only if the functions are closed, this has to be done after the closure conversion.
liftFunctions :: Instruction -> ([FunctionDef], Instruction)
liftFunctions (Function f args body c) =
  let (funs, c') = liftFunctions c
      (funs', body') = liftFunctions body in
  ((f,args,body'):(funs' ++ funs), c')

liftFunctions (Array array x c) =
  let (funs, c') = liftFunctions c in
  (funs, Array array x c')

liftFunctions (Access n x y c) =
  let (funs, c') = liftFunctions c in
  (funs, Access n x y c')

liftFunctions (Switch v cases def) =
  let (funs, cases') = List.foldl (\(fs, cl) (n, c) ->
        let (fs', c') = liftFunctions c in
        (fs' ++ fs, (n,c'):cl)) ([], []) cases
      (funs', def') = liftFunctions def in

  (funs ++ funs', Switch v (List.reverse cases') def')

liftFunctions (Call f args x c) =
  let (funs, c') = liftFunctions c in
  (funs, Call f args x c')

liftFunctions c =
 ([], c)


---------------------------------------------------------------------------------------------------
-- * Code optimization.

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
--check_cexpr :: [Variable] -> Instruction -> Compiler ()
--check_cexpr scope (Function g arg body c) = do
--  let nscope = List.union scope arg
--  check_cexpr nscope body
--  check_cexpr (g:scope) c
--check_cexpr scope (TailCall f arg) = do
--  check_value scope f
--  List.foldl (\rec a -> do
--        rec
--        check_value scope a) (return ()) arg
--check_cexpr scope (Call f arg x c) = do
--  check_value scope f
--  List.foldl (\rec a -> do
--        rec
--        check_value scope a) (return ()) arg
--  check_cexpr (x:scope) c
--check_cexpr scope (Array vals x c) = do
--  List.foldl (\rec v -> do
--        rec
--        check_value scope v) (return ()) vals
--  check_cexpr (x:scope) c
--check_cexpr scope (Access n v x c) = do
--  check_value scope v
--  check_cexpr (x:scope) c
--check_cexpr scope (Switch v clist c) = do
--  check_value scope v
--  List.foldl (\rec (_,c) -> do
--        rec
--        check_cexpr scope c) (return ()) clist
--  check_cexpr scope c
--check_cexpr scope (Ret v) =
--  check_value scope v
--check_cexpr scope (Set x v) =
--  check_value scope v
--check_cexpr scope (Error msg) =
--  return ()


-- | Check the scope of the variables of a compile unit.
--check_cunit :: CompilationUnit -> Compiler ()
--check_cunit cu = do
--  let scope = List.map (\(f,_,_) -> f) (local cu) ++ List.map (\(f,_,_) -> f) (externFunctions cu) ++ List.map fst (globalVariables cu)
--  List.foldl (\rec (_, arg, c) -> do
--        rec
--        check_cexpr (List.union arg scope) c) (return ()) (local cu ++ externFunctions cu)
--  case main cu of
--    Just c -> check_cexpr scope c
--    Nothing -> return ()

-- | Pretty-print a value using Hughes's and Peyton Jones's pretty printing combinators. The type
-- 'Doc' is defined in the library "Text.PrettyPrint.HughesPJ" and allows for nested documents.
valueToDoc :: (Variable -> String)  -- ^ Rendering of term variables.
            -> Value                 -- ^ Instruction to print.
            -> Doc                   -- ^ Resulting PP document.
valueToDoc _ (VInt n) = text $ show n
valueToDoc pVar (VVar v) = text $ pVar v
valueToDoc pVar (VGlobal v) = text $ pVar v
valueToDoc pVar (VLabel v) = text $ pVar v

-- | Pretty-print an expression using Hughes's and Peyton Jones's pretty printing combinators. The
-- type 'Doc' is defined in the library "Text.PrettyPrint.HughesPJ" and allows for nested documents.
functionToDoc :: (Variable -> String)                   -- ^ Rendering of term variables.
           -> (Variable, [Variable], Instruction)       -- ^ Function to print.
           -> Doc                                       -- ^ Resulting PP document.
functionToDoc pVar (f, [], body) =
  text (pVar f ++ "() {") $$
  nest 2 (instructionToDoc Inf pVar body) $$
  text "}"
functionToDoc pVar (f, args, body) =
  let args' = punctuate comma $ List.map (text . pVar) args in
  text (pVar f ++ "(") <> hsep args' <> text ") {" $$
  nest 2 (instructionToDoc Inf pVar body) $$
  text "}"


-- | Pretty-print a continuation function using Hughes's and Peyton Jones's pretty printing combinators.
-- The type 'Doc' is defined in the library "Text.PrettyPrint.HughesPJ" and allows for nested documents.
instructionToDoc :: Lvl              -- ^ Maximum depth.
            -> (Variable -> String)  -- ^ Rendering of term variables.
            -> Instruction           -- ^ Instruction to print.
            -> Doc                   -- ^ Resulting PP document.
instructionToDoc _ pVar (Call f args x c) =
  let args' = punctuate comma $ List.map (valueToDoc pVar) args in
  text (pVar x) <+> text ":=" <+> valueToDoc pVar f <> text "(" <> hsep args' <> text ");" $$
  instructionToDoc Inf pVar c
instructionToDoc _ pVar (TailCall f args) =
  let args' = punctuate comma $ List.map (valueToDoc pVar) args in
  valueToDoc pVar f <> text "(" <> hsep args' <> text ");"
instructionToDoc _ pVar (Array array x c) =
  let array' = punctuate comma $ List.map (valueToDoc pVar) array in
  text (pVar x ++ " := [") <> hsep array' <> text "];" $$
  instructionToDoc Inf pVar c
instructionToDoc _ pVar (Access n x y c) =
  text (pVar y ++ " :=") <+> valueToDoc pVar x <> text ("[" ++ show n ++ "];") $$
  instructionToDoc Inf pVar c
instructionToDoc _ pVar (Switch v cases def) =
  let cases' = List.map (\(n,c) -> (n, instructionToDoc Inf pVar c)) cases
      def' = text "default:" $$ nest 2 (instructionToDoc Inf pVar def) in
  text "switch" <+> valueToDoc pVar v <+> text "with" $$
  nest 2 (List.foldl (\doc (tag, c) ->
      doc $$
      text (show tag ++ ":") $$
      nest 2 c) PP.empty cases' $$ def')
instructionToDoc _ pVar (Function f args body c) =
  functionToDoc pVar (f, args, body) $$
  instructionToDoc Inf pVar c
instructionToDoc _ pVar (Set x v) =
  text (pVar x) <+> text ":=" <+> valueToDoc pVar v
instructionToDoc _ pVar (Ret v) =
  text "ret" <+> valueToDoc pVar v
instructionToDoc _ pVar (Error msg) =
  text "error \"" <> text msg <> text "\""


instance PPrint Instruction where
  -- Generic printing
  genprint lv [pVar] e =
    let doc = instructionToDoc lv pVar e in
    PP.render doc
  genprint lv _ e =
    throwNE $ ProgramError "CPS:genprint(Instruction): illegal argument"

  -- Other
  -- By default, the term variables are printed as x_n and the data constructors as D_n,
  -- where n is the id of the variable / constructor
  sprintn lv e = genprint lv [prevar "%"] e


instance PPrint CompilationUnit where
  genprint _ [pVar] unit =
    let funs = List.map (functionToDoc pVar) (externFunctions unit ++ localFunctions unit) in
    let (gdef, ginit) = List.unzip $ List.map (\(g, e) ->
          (text (pVar g), instructionToDoc Inf pVar e)) $ globalVariables unit in
    let imports' = List.map (\v -> case v of
          VLabel x -> text $ pVar x
          VGlobal x -> text $ pVar x
          _ -> text "WATWATWAT") $ imports unit in
    let main' = case main unit of
          Just m ->
            text "main () {" $$
            nest 2 (instructionToDoc Inf pVar m) $$
            text "}" $$ text " "
          Nothing -> text " " in
    let all =
          text "extern" <+> hsep (punctuate comma imports') $$
          text "globals" <+> hsep (punctuate comma gdef) $$ text " " $$
          text "init () {" $$ nest 2 (vcat ginit) $$ text "}" $$ text " " $$
          main' $$
          vcat funs in
    PP.render all

  genprint _ _ _ =
    throwNE $ ProgramError "CPS:genprint(CompilationUnit): illegal argument"

  sprintn lv e = genprint lv [prevar "%"] e
