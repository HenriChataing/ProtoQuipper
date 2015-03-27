{-# LANGUAGE MultiParamTypeClasses #-}

-- | This module contains the definition of the last language used before the cnstruction of the LLVM module.
-- It explicitates the flow control, and uses only simple operations.
module Compiler.CExpr where

import Prelude hiding (lookup)

import Utils
import Classes hiding ((<+>), (\\))

import Monad.Compiler
import Monad.Error

import qualified Core.Syntax as CS

import qualified Compiler.SimplSyntax as S
import Compiler.Circuits

import Data.List ((\\))
import qualified Data.List as List
import Text.PrettyPrint.HughesPJ as PP
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap



-- | The definition of values.
data Value =
    VVar Variable              -- ^ A local variable _ function or not.
  | VInt Int                   -- ^ An integer.
  | VLabel Variable            -- ^ The label of an extern function.
  | VGlobal Variable           -- ^ A reference to a global variable.
  deriving (Show, Eq)

-- | Destruct a 'VVar' value.
unVVar :: Value -> Variable
unVVar (VVar x) = x
unVVar _ = throwNE $ ProgramError "CExpr:unVVar: illegal argument"


-- | Are considered free variables only variables bound in a local scope.
instance TermObject Value where
  freevar (VVar x) = [x]
  freevar _ = []


instance Subs Value Value where
  subs x v (VVar y) = if x == y then v else VVar y
  subs _ _ v = v


-- | Context of values used during the translation.
type CContext = IntMap Value


-- | Retrieve a value from the context.
value :: CContext -> Variable -> Value
value vals x =
  case IMap.lookup x vals of
    Just v -> v
    Nothing -> VVar x


-- | Definition of expressions.
data CExpr =
    CFun Variable [Variable] CExpr CExpr           -- ^ Function abstraction: @fun x1 .. xN -> t@. All definitions are recursive.
  | CTailApp Value [Value]                         -- ^ Application of a function in tail position: @t u@.
  | CApp Value [Value] Variable CExpr              -- ^ Application of a function, with a continuation.
  | CTuple [Value] Variable CExpr                  -- ^ Construction of a tuple: @(/t/1, .. , /t//n/)@.
  | CAccess Int Value Variable CExpr               -- ^ Access the nth element of a tuple.
  | CSwitch Value [(Int, CExpr)] CExpr             -- ^ Switch condition (with a default target).
  | CRet Value                                     -- ^ Return a value. This instruction is terminal.
  | CSet Variable Value                            -- ^ This instruction is terminal, and specific to global variables, where it is necessary to set a specific variable.
  | CFree Value CExpr                              -- ^ Assuming the value represents a tuple, free the memory and continue with the expression.
  | CError String                                  -- ^ This instruction is terminal, and throws an error message.
  deriving Show



instance TermObject CExpr where
  free_var (CFun f args cf c) =
    List.union (free_var cf \\ (f:args)) (free_var c \\ [f])
  free_var (CApp f args x c) =
    List.foldl (\fv a ->
          List.union (free_var a) fv) (free_var c \\ [x]) (f:args)
  free_var (CTailApp f args) =
    List.foldl (\fv a ->
          List.union (free_var a) fv) [] (f:args)
  free_var (CTuple vlist x c) =
    let fvl = List.foldl (\fv a ->
          List.union (free_var a) fv) [] vlist in
    List.union (free_var c \\ [x]) fvl
  free_var (CAccess _ v x c) =
    List.union (free_var c \\ [x]) (free_var v)
  free_var (CSwitch v clist def) =
    List.foldl (\fv (_,c) ->
          List.union (free_var c) fv) (free_var v) $ (0,def):clist
  free_var (CSet x v) = free_var v -- x is ignored here because a global variable.
  free_var (CRet v) = free_var v
  free_var (CFree v c) = List.union (free_var v) (free_var c)
  free_var (CError _) = []


instance Subs CExpr Value where
  subs x v (CFun f args cf c) =
    CFun f args (subs x v cf) (subs x v c)
  subs x v (CApp f args y c) =
    CApp (subs x v f) (List.map (subs x v) args) y $ subs x v c
  subs x v (CTailApp f args) =
    CTailApp (subs x v f) $ List.map (subs x v) args
  subs x v (CTuple vlist y c) =
    CTuple (List.map (subs x v) vlist) y $ subs x v c
  subs x v (CAccess n w y c) =
    CAccess n (subs x v w) y $ subs x v c
  subs x v (CSwitch w clist def) =
    CSwitch (subs x v w) (List.map (\(n, c) -> (n, subs x v c)) clist) $ subs x v def
  subs x v (CSet y w) =
    CSet y $ subs x v w
  subs x v (CRet w) =
    CRet $ subs x v w
  subs x v (CFree w c) =
    CFree (subs x v w) (subs x v c)
  subs _ _ (CError msg) =
    CError msg




-- | Compilation unit.
data CUnit = CUnit {
  imports :: [Value],                      -- ^ The list of functions and variables imported from extern modules.
  strings :: [Variable],                   -- ^ The list of constant strings used by the compile unit.
  local :: [FunctionDef],                  -- ^ The list of local functions.
  extern :: [FunctionDef],                 -- ^ The list of functions accessible outside of the module.
  vglobals :: [GlobalDef],                 -- ^ Contains the list of global variables, along with the code initializing these variables.
  main :: Maybe CExpr                      -- ^ The definition of the main function, if the module is \'Main\'.
}


-- | The type of function declarations.
type FunctionDef = (Variable, [Variable], CExpr)

-- | The type of global variable declarations.
type GlobalDef = (Variable, CExpr)

-- | The type of conversion functions.
type Conversion = (CContext -> (Value -> QpState CExpr) -> S.Expr -> QpState CExpr)


-- | Convert an expression from the simplified syntax to the continuation passing style.
convert_to_cps :: CContext                        -- ^ Current context.
               -> (Value -> QpState CExpr)        -- ^ A continuation.
               -> S.Expr                          -- ^ Argument expression.
               -> QpState CExpr                   -- ^ The resulting continuation expression.

convert_to_cps vals c (S.EVar x) =
  case value vals x of
    -- global functions when handled as objects must be boxed
    VLabel gx -> do
        cf <- create_var "f"      -- function closure
        cx <- c (VVar cf)
        return $ CTuple [VLabel gx] cf cx
    -- global variables when handled as objects must be unboxed
    VGlobal gx -> do
        ug <- create_var "ug"
        cug <- c (VVar ug)
        return $ CAccess 0 (VGlobal gx) ug cug
    v ->
        c v

convert_to_cps vals c (S.EGlobal x) =
  convert_to_cps vals c (S.EVar x)

convert_to_cps vals c (S.EInt n) =
  c (VInt n)

convert_to_cps vals c (S.EBool b) =
  c (if b then VInt 1 else VInt 0)

convert_to_cps vals c S.EUnit =
  c (VInt 0)

convert_to_cps vals c (S.ETuple []) =
  c (VInt 0)

convert_to_cps vals c (S.ETuple elist) = do
  x <- create_var "x"
  aux elist (\w -> do
        cx <- c (VVar x)
        return $ CTuple w x cx)
  where
    aux l c = do
      let aux' [] w = c (List.reverse w)
          aux' (e:es) w = convert_to_cps vals (\v -> aux' es (v:w)) e
      aux' l []

convert_to_cps vals c (S.EAccess n x) = do
  y <- create_var "x"
  cy <- c (VVar y)
  return $ CAccess n (value vals x) y cy

convert_to_cps vals c (S.EFun x e) = do
  f <- create_var "f"       -- function name
  k <- create_var "k"       -- continuation argument
  -- At the end of the body, the result is passed to the continuation k
  body <- convert_to_cps vals (\z -> return $ CTailApp (VVar k) [z]) e
  -- The reference f of the function is passed to the building continuation c
  cf <- c (VVar f)
  return $ CFun f [x, k] body $ cf

convert_to_cps vals c (S.EFix f x e) = do
  k <- create_var "k"       -- continuation argument
  -- At the end of the body, the result is passed to the continuation k
  let vals' = IMap.insert f (VVar f) vals
  body <- convert_to_cps vals' (\z -> return $ CTailApp (VVar k) [z]) e
  -- The reference f of the function is passed to the building continuation c
  cf <- c (VVar f)
  return $ CFun f [x, k] body $ cf

-- the direct application of global functions is treated separately.
convert_to_cps vals c (S.EApp (S.EVar f) arg) = do
  r <- create_var "r"       -- return address
  x <- create_var "x"       -- argument of the return address
  case value vals f of
    VLabel f -> do
        app <- convert_to_cps vals (\arg ->
              return $ CTailApp (VLabel f) [arg, VVar r]) arg
        cx <- c (VVar x)
        return $ CFun r [x] cx app
    _ -> do
        app <- convert_to_cps vals (\f ->
              convert_to_cps vals (\arg ->
              return $ CTailApp f [arg, VVar r]) arg) (S.EVar f)
        cx <- c (VVar x)
        return $ CFun r [x] cx app

convert_to_cps vals c (S.EApp (S.EGlobal f) arg) =
  convert_to_cps vals c (S.EApp (S.EVar f) arg)

convert_to_cps vals c (S.EApp f arg) = do
  r <- create_var "r"       -- return address
  x <- create_var "x"       -- argument of the return address
  app <- convert_to_cps vals (\f ->
        convert_to_cps vals (\arg ->
              return $ CTailApp f [arg, VVar r]) arg) f
  cx <- c (VVar x)
  return $ CFun r [x] cx app

convert_to_cps vals c (S.ESeq e f) = do
  convert_to_cps vals (\z -> convert_to_cps vals c f) e

convert_to_cps vals c (S.ELet x e f) = do
  convert_to_cps vals (\z -> do
        convert_to_cps (IMap.insert x z vals) c f) e

convert_to_cps vals c (S.EMatch e blist def) = do
  k <- create_var "k"
  x <- create_var "x"
  cx <- c (VVar x)
  let slist = List.sortBy (\(n,_) (m,_) -> compare n m) blist
  elist' <- List.foldl (\rec (n, e) -> do
        es <- rec
        e' <- convert_to_cps vals (\z -> return $ CTailApp (VVar k) [z]) e
        return $ (n,e'):es) (return []) slist
  def' <- convert_to_cps vals (\z -> return $ CTailApp (VVar k) [z]) def
  convert_to_cps vals (\e ->
        return $ CFun k [x] cx $
                 CSwitch e (List.reverse elist') def') e

convert_to_cps vals _ (S.EError msg) = do
  return $ CError msg


-- | Convert an expression from the simplified syntax to a weak form of the continuation passing style, where only branching conditions impose the use of continuations.
convert_to_wcps :: CContext                        -- ^ Current context.
               -> (Value -> QpState CExpr)        -- ^ A continuation.
               -> S.Expr                          -- ^ Argument expression.
               -> QpState CExpr                   -- ^ The resulting continuation expression.
convert_to_wcps vals c (S.EVar x) =
  case value vals x of
    -- global functions when handled as objects must be boxed
    VLabel gx -> do
        cf <- create_var "f"      -- function closure
        cx <- c (VVar cf)
        return $ CTuple [VLabel gx] cf cx
    -- global variables when handled as objects must be unboxed
    VGlobal gx -> do
        ug <- create_var "ug"
        cug <- c (VVar ug)
        return $ CAccess 0 (VGlobal gx) ug cug
    v ->
        c v

convert_to_wcps vals c (S.EGlobal x) =
  convert_to_wcps vals c (S.EVar x)

convert_to_wcps vals c (S.EInt n) =
  c (VInt n)

convert_to_wcps vals c (S.EBool b) =
  c (if b then VInt 1 else VInt 0)

convert_to_wcps vals c S.EUnit =
  c (VInt 0)

convert_to_wcps vals c (S.ETuple []) =
  c (VInt 0)

convert_to_wcps vals c (S.ETuple elist) = do
  x <- create_var "x"
  aux elist (\w -> do
        cx <- c (VVar x)
        return $ CTuple w x cx)
  where
    aux l c = do
      let aux' [] w = c (List.reverse w)
          aux' (e:es) w = convert_to_wcps vals (\v -> aux' es (v:w)) e
      aux' l []

convert_to_wcps vals c (S.EAccess n x) = do
  y <- create_var "x"
  cy <- c (VVar y)
  return $ CAccess n (value vals x) y cy

convert_to_wcps vals c (S.EFun x e) = do
  f <- create_var "f"       -- function name
  -- At the end of the body, the result is returned using CRet
  body <- convert_to_wcps vals (\z -> return $ CRet z) e
  -- The reference f of the function is passed to the building continuation c
  cf <- c (VVar f)
  return $ CFun f [x] body $ cf

convert_to_wcps vals c (S.EFix f x e) = do
  -- At the end of the body, the result is returned using CRet k
  let vals' = IMap.insert f (VVar f) vals
  body <- convert_to_wcps vals' (\z -> return $ CRet z) e
  -- The reference f of the function is passed to the building continuation c
  cf <- c (VVar f)
  return $ CFun f [x] body $ cf

-- the direct application of global functions is treated separately.
convert_to_wcps vals c (S.EApp (S.EVar f) arg) = do
  x <- create_var "x"    -- result of the application
  case value vals f of
    VLabel f -> do
        cx <- c (VVar x)
        convert_to_wcps vals (\arg ->
              return $ CApp (VLabel f) [arg] x cx) arg
    _ -> do
        cx <- c (VVar x)
        convert_to_wcps vals (\f ->
              convert_to_wcps vals (\arg ->
                    return $ CApp f [arg] x cx) arg) (S.EVar f)

convert_to_wcps vals c (S.EApp (S.EGlobal f) arg) =
  convert_to_wcps vals c (S.EApp (S.EVar f) arg)

convert_to_wcps vals c (S.EApp f arg) = do
  x <- create_var "x"       -- result of the application
  cx <- c (VVar x)
  convert_to_wcps vals (\f ->
        convert_to_wcps vals (\arg ->
              return $ CApp f [arg] x cx) arg) f

convert_to_wcps vals c (S.ESeq e f) = do
  convert_to_wcps vals (\z -> convert_to_wcps vals c f) e

convert_to_wcps vals c (S.ELet x e f) = do
  convert_to_wcps vals (\z -> do
        convert_to_wcps (IMap.insert x z vals) c f) e

convert_to_wcps vals c (S.EMatch e blist def) = do
  -- until a better solution is found, each branch finishes with a call to the function implementing the continuation
  k <- create_var "k"
  x <- create_var "x"
  cx <- c (VVar x)
  let slist = List.sortBy (\(n,_) (m,_) -> compare n m) blist
  elist' <- List.foldl (\rec (n, e) -> do
        es <- rec
        e' <- convert_to_wcps vals (\z -> return $ CTailApp (VVar k) [z]) e
        return $ (n,e'):es) (return []) slist
  def' <- convert_to_wcps vals (\z -> return $ CTailApp (VVar k) [z]) def
  convert_to_wcps vals (\e ->
        return $ CFun k [x] cx $
                 CSwitch e (List.reverse elist') def') e

convert_to_wcps _ _ (S.EError msg) = do
  return $ CError msg


-- | Convert the toplevel declarations into CPS form.
convert_declarations_to_cps :: [S.Declaration]            -- ^ List of declarations.
                            -> QpState CUnit              -- ^ Resulting compile unit.
convert_declarations_to_cps decls = do
  -- build the list of imported variables
  let imported = List.foldl (\imp (S.DLet _ _ e) -> List.union (S.imports e) imp) [] decls
  (ivals, imported) <- List.foldl (\rec ix -> do
        (ivals, imported) <- rec
        tix <- global_type ix
        if CS.is_fun tix then
          return (IMap.insert ix (VLabel ix) ivals, (VLabel ix):imported)
        else
          return (IMap.insert ix (VGlobal ix) ivals, (VGlobal ix):imported)) (return (IMap.empty, [])) imported

  -- translate the declarations
  (cu, _) <- List.foldl (\rec (S.DLet vis f e) -> do
        (cu, vals) <- rec
        n <- variable_name f
        -- TODO XXX Check the type of the main function.
        case (n,e) of
          ("main", S.EFun _ c) -> do
              body <- convert_to_cps vals (\z -> return $ CRet z) c
              body <- return $ constant_folding 3 body
              (funs, body) <- closure_conversion body >>= return . lift_functions
              return (cu { main = Just body, local = funs ++ local cu }, vals)

          (_, S.EFun x c) -> do
              k <- create_var "k"       -- continuation argument
              fc <- create_var "fc"     -- closure argument
              body <- convert_to_cps vals (\z -> return $ CTailApp (VVar k) [z]) c
              body <- return $ constant_folding 3 body
              (funs, body) <- closure_conversion body >>= return . lift_functions
              let fdef = (f, [fc,x,k], body)
              case vis of
                S.Internal ->
                    return (cu { local = funs ++ [fdef] ++ local cu }, IMap.insert f (VLabel f) vals)
                S.External ->
                    return (cu { local = funs ++ local cu, extern = fdef:(extern cu) }, IMap.insert f (VLabel f) vals)

          (_, S.EFix _ x c) -> do
              k <- create_var "k"       -- continuation argument
              fc <- create_var "fc"     -- closure argument
              let vals' = IMap.insert f (VLabel f) vals
              body <- convert_to_cps vals' (\z -> return $ CTailApp (VVar k) [z]) c
              body <- return $ constant_folding 3 body
              (funs, body) <- closure_conversion body >>= return . lift_functions
              let fdef = (f, [fc,x,k], body)
              case vis of
                S.Internal ->
                    return (cu { local = funs ++ [fdef] ++ local cu }, vals')
                S.External ->
                    return (cu { local = funs ++ local cu, extern = fdef:(extern cu) }, vals')

          _ -> do
              -- translate the computation of g
              init <- convert_to_cps vals (\z -> return $ CSet f z) e
              (funs,init) <- closure_conversion init >>= return . lift_functions
              -- return the extend compile unit
              return (cu { local = funs ++ local cu, vglobals = (f, init):(vglobals cu) }, IMap.insert f (VGlobal f) vals)

    ) (return (CUnit { local = [], extern = [], vglobals = [], imports = imported, strings = [], main = Nothing }, ivals)) decls
  return cu { extern = List.reverse $ extern cu, vglobals = List.reverse $ vglobals cu }


-- | Convert the toplevel declarations into wCPS form.
convert_declarations_to_wcps :: [S.Declaration]            -- ^ List of declarations.
                             -> QpState CUnit              -- ^ Resulting compile unit.
convert_declarations_to_wcps decls = do
  -- build the list of imported variables
  let imported = List.foldl (\imp (S.DLet _ _ e) -> List.union (S.imports e) imp) [] decls
  (ivals, imported) <- List.foldl (\rec ix -> do
        (ivals, imported) <- rec
        tix <- global_type ix
        if CS.is_fun tix then
          return (IMap.insert ix (VLabel ix) ivals, (VLabel ix):imported)
        else
          return (IMap.insert ix (VGlobal ix) ivals, (VGlobal ix):imported)) (return (IMap.empty, [])) imported

  -- translate the declarations
  (cu, _) <- List.foldl (\rec (S.DLet vis f e) -> do
        (cu, vals) <- rec
        n <- variable_name f
        case (n, e) of
          ("main", S.EFun _ c) -> do
              body <- convert_to_wcps vals (\z -> return $ CRet z) c
              body <- return $ constant_folding 3 body
              (funs, body) <- closure_conversion body >>= return . lift_functions
              return (cu { main = Just body, local = funs ++ local cu }, vals)

          (_, S.EFun x c) -> do
              fc <- create_var "fc"     -- closure argument
              body <- convert_to_wcps vals (\z -> return $ CRet z) c
              body <- return $ constant_folding 3 body
              (funs, body) <- closure_conversion body >>= return . lift_functions
              let fdef = (f, [fc,x], body)
              case vis of
                S.Internal ->
                    return (cu { local = funs ++ [fdef] ++ local cu },
                            IMap.insert f (VLabel f) vals)
                S.External ->
                    return (cu { local = funs ++ local cu, extern = fdef:(extern cu) },
                            IMap.insert f (VLabel f) vals)

          (_, S.EFix _ x c) -> do
              fc <- create_var "fc"     -- closure argument
              let vals' = IMap.insert f (VLabel f) vals
              body <- convert_to_wcps vals' (\z -> return $ CRet z) c
              body <- return $ constant_folding 3 body
              (funs, body) <- closure_conversion body >>= return . lift_functions
              let fdef = (f, [fc,x], body)
              case vis of
                S.Internal ->
                    return (cu { local = funs ++ [fdef] ++ local cu }, vals')
                S.External ->
                    return (cu { local = funs ++ local cu, extern = fdef:(extern cu) }, vals')

          _ -> do
              -- translate the computation of g
              init <- convert_to_wcps vals (\z -> return $ CSet f z) e
              (funs,init) <- closure_conversion init >>= return . lift_functions
              -- return the extend compile unit
              return (cu { local = funs ++ local cu, vglobals = (f, init):(vglobals cu) }, IMap.insert f (VGlobal f) vals)

    ) (return (CUnit { local = [], extern = [], vglobals = [], imports = imported, strings = [], main = Nothing }, ivals)) decls
  return cu { extern = List.reverse $ extern cu, vglobals = List.reverse $ vglobals cu }




-- | Closure conversion of the CPS code. This auxiliary function also returns the set of free variables of the produced expression.
closure_conversion_aux :: IntMap (Usage, Information) -> CExpr -> QpState (CExpr, [Variable])
closure_conversion_aux info (CFun f args cf c) = do
  -- Check the usage iof the function [f].
  case IMap.lookup f info of
    Just (usage@Usage { escapes = 0 } , _) -> do
        -- The function doesn't need to be closed.
        -- Instead, the free variables are passed as arguments.

        -- Free variables of f.
        let fv = free_var cf \\ (f:args)
        -- Update the information about [f] to convey the free variables.
        let info' = IMap.insert f (usage, IFun fv cf) info
        (cf', _) <- closure_conversion_aux info' cf
        (c', fvc) <- closure_conversion_aux info' c
        return (CFun f (args ++ fv) cf' c', List.union fv (fvc \\ [f]))
    _ -> do
        (cf', fvcf) <- closure_conversion_aux info cf
        (c', fvc) <- closure_conversion_aux info c
        let fv = fvcf \\ (f:args)
        -- Extraction of the free variables of cf'.
        let cf'' = List.foldl (\cf (x,n) ->
              CAccess n (VVar f) x cf) cf' $ List.zip fv [1..List.length fv]
        -- Construction of the closure (with continuation c' and name f).
        let c'' = CTuple (VVar f:(List.map VVar fv)) f c'
        -- Re-definition of the function f.
        return (CFun f (f:args) cf'' c'', List.union fv (fvc \\ [f]))

closure_conversion_aux info (CApp (VVar f) args x c) = do
  -- Check the usage of the function [f].
  case IMap.lookup f info of
    Just (Usage { escapes = 0 }, IFun fv _) -> do
        -- The function is known: no closure argument, instead
        -- the free variables added to the list of arguments.
        (c', fvc) <- closure_conversion_aux info c
        return ( CApp (VVar f) (args ++ List.map VVar fv) x c',
                 List.union (fvc \\ [x]) (f:(List.union fv $ List.concat $ List.map free_var args)))
    _ -> do
        (c', fvc) <- closure_conversion_aux info c
        f' <- create_var "f"
        return ( CAccess 0 (VVar f) f' $                     -- Extract the function pointer
                 CApp (VVar f') (VVar f:args) x c',          -- Apply the function to its own closure
                 List.union (fvc \\ [x]) (f:(List.concat $ List.map free_var args)) )

-- since global functions are already closed, only a dummy closure is passed as argument.
closure_conversion_aux info (CApp (VLabel f) args x c) = do
  (c', fvc) <- closure_conversion_aux info c
  return ( CApp (VLabel f) (VInt 0:args) x c',         -- Apply the function to a dummy closure (0)
           List.union (fvc \\ [x]) (List.concat $ List.map free_var args) )

closure_conversion_aux info (CTailApp (VVar f) args) = do
  -- Check the usage of the function [f].
  case IMap.lookup f info of
    Just (Usage { escapes = 0 }, IFun fv _) -> do
        -- The function is known: no closure argument, instead
        -- the free variables added to the list of arguments.
        return ( CTailApp (VVar f) (args ++ List.map VVar fv),
                  f:(List.union fv $ List.concat $ List.map free_var args))
    _ -> do
        f' <- create_var "f"
        return ( CAccess 0 (VVar f) f' $                     -- Extract the function pointer
                 CTailApp (VVar f') (VVar f:args),           -- Apply the function to its own closure
                 f:(List.concat $ List.map free_var args) )

-- since global functions are already closed, only a dummy closure is passed as argument.
closure_conversion_aux info (CTailApp (VLabel f) args) = do
  return ( CTailApp (VLabel f) (VInt 0:args),               -- Apply the function to a dummy closure (1)
           List.concat $ List.map free_var args )

closure_conversion_aux info (CTuple vlist x c) = do
  (c', fvc) <- closure_conversion_aux info c
  let fv = List.nub $ List.concat $ List.map free_var vlist
  return (CTuple vlist x c', List.union fv (fvc \\ [x]))

closure_conversion_aux info (CAccess n v x c) = do
  (c', fvc) <- closure_conversion_aux info c
  return (CAccess n v x c', List.union (free_var v) (fvc \\ [x]))

closure_conversion_aux info (CSwitch v clist def) = do
  (clist', fvc) <- List.foldl (\rec (n,c) -> do
        (cl, fvc) <- rec
        (c', fvc') <- closure_conversion_aux info c
        return ((n,c'):cl, List.union fvc' fvc)) (return ([], [])) clist
  (def', fvdef) <- closure_conversion_aux info def
  return (CSwitch v (List.reverse clist') def', List.union (free_var v) $ List.union fvc fvdef)

closure_conversion_aux _ e =
  return (e, free_var e)


-- | Closure conversion of the CPS code.
closure_conversion :: CExpr -> QpState CExpr
closure_conversion e = do
  (e, _) <- closure_conversion_aux (gather IMap.empty e) e
  return e



-- | Lift the function definitions to the top of the module.
-- This function separates the function definitions from the rest of the continuation expression.
-- Since this operation is sound only if the functions are closed, this has to be done after the closure conversion.
lift_functions :: CExpr -> ([FunctionDef], CExpr)
lift_functions (CFun f args cf c) =
  let (funs, c') = lift_functions c
      (funs', cf') = lift_functions cf in
  ((f,args,cf'):(funs' ++ funs), c')

lift_functions (CTuple vlist x c) =
  let (funs, c') = lift_functions c in
  (funs, CTuple vlist x c')

lift_functions (CAccess n x y c) =
  let (funs, c') = lift_functions c in
  (funs, CAccess n x y c')

lift_functions (CSwitch v clist def) =
  let (funs, clist') = List.foldl (\(fs, cl) (n,c) ->
        let (fs', c') = lift_functions c in
        (fs' ++ fs, (n,c'):cl)) ([], []) clist
      (funs', def') = lift_functions def in

  (funs ++ funs', CSwitch v (List.reverse clist') def')

lift_functions (CApp f args x c) =
  let (funs, c') = lift_functions c in
  (funs, CApp f args x c')

lift_functions c =
 ([], c)



-- | Check a value.
check_value :: [Variable] -> Value -> QpState ()
check_value scope (VVar v) =
  if List.elem v scope then return ()
  else do
    n <- variable_name v
    fail $ "CExpr:check_value: undefined variable " ++ n
check_value scope _ =
  return ()


-- * This section is dedicated to code optimization.


-- | Usage information : number of uses and escapes.
data Usage = Usage { uses :: Int, escapes :: Int }

-- | No usage.
no_usage :: Usage
no_usage = Usage { uses = 0, escapes = 0 }


-- | Describe for each kind of bound variable the information
-- needed for the optimizations.
data Information =
    IFun [Variable] CExpr
  | ITuple [Value]
  | IAccess Variable Int
  | IParam
  | ICall
  | IOther


-- | Update the information regarding a variable.
update_information :: ((Usage, Information) -> Maybe (Usage, Information)) -> IntMap (Usage, Information) -> Value -> IntMap (Usage, Information)
update_information f info (VVar x) = IMap.update f x info
update_information f info (VLabel x) = IMap.update f x info
update_information f info (VGlobal x) = IMap.update f x info
update_information _ info _ = info


-- | Increase the number of uses of a variable.
increase_uses :: IntMap (Usage, Information) -> Value -> IntMap (Usage, Information)
increase_uses = update_information (\(usage, info) -> Just (usage { uses = uses usage + 1 }, info))


-- | Increase the number of uses of a variable.
increase_escapes :: IntMap (Usage, Information) -> Value -> IntMap (Usage, Information)
increase_escapes = update_information (\(usage, info) -> Just (usage { escapes = escapes usage + 1 }, info))


-- | Lookup the information about a value.
lookup_information :: Value -> IntMap (Usage, Information) -> Maybe (Usage, Information)
lookup_information (VVar x) info = IMap.lookup x info
lookup_information (VLabel x) info = IMap.lookup x info
lookup_information (VGlobal x) info = IMap.lookup x info
lookup_information _ _ = Nothing


-- | Do a pass to gather information.
gather :: IntMap (Usage, Information) -> CExpr -> IntMap (Usage, Information)
gather info (CFun g arg body c) =
  let info' = List.foldl (\info a -> IMap.insert a (no_usage, IParam) info) (IMap.insert g (no_usage, IFun arg body) info) arg in
  gather (gather info' body) c
gather info (CTailApp f arg) =
  List.foldl increase_escapes (increase_uses info f) arg
gather info (CApp f arg x c) =
  let info' = List.foldl increase_escapes (increase_uses info f) arg in
  gather (IMap.insert x (no_usage, ICall) info') c
gather info (CTuple vals x c) =
  let info' = List.foldl increase_escapes info vals in
  gather (IMap.insert x (no_usage, ITuple vals) info') c
gather info (CAccess n v x c) =
  let info' = increase_uses info v in
  gather (IMap.insert x (no_usage, IAccess (unVVar v) n) info') c
gather info (CSwitch v clist c) =
  let info' = increase_uses info v in
  List.foldl (\info (_,c) -> gather info c) (gather info' c) clist
gather info (CRet v) =
  increase_escapes info v
gather info (CSet x v) =
  -- Since [x] here is supposed to be a global variable, no need
  -- to track it down.
  increase_escapes info v
gather info (CFree v c) =
  gather (increase_uses info v) c
gather info (CError msg) =
  info



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
constant_folding :: Int -> CExpr -> CExpr
constant_folding n c =
  if not ((n > 0) && (n < 5)) then
    throwNE $ ProgramError "CExpr:constant_folding: illegal number of iterations"
  else
    let opt info (CFun f arg body c) =
          -- Optimize the body.
          let body' = opt info body in
          CFun f arg body' (opt info c)
        opt info (CTailApp f vals) =
          CTailApp f vals
        opt info (CApp f vals x c) =
          CApp f vals x $ opt info c
        opt info (CTuple vals x c) =
          case IMap.lookup x info of
            Just (usage, inf) ->
                -- If the tuple is not used, remove it.
                if uses usage + escapes usage == 0 then
                  opt info c
                else CTuple vals x $ opt info c
            Nothing -> CTuple vals x $ opt info c
        opt info (CAccess n v x c) =
          case IMap.lookup x info of
            Just (usage, inf) ->
                -- If the tuple is not used, remove it.
                if uses usage + escapes usage == 0 then
                  opt info c
                else
                  case lookup_information v info of
                    Just (_, ITuple vals) ->
                        -- In case the value being accessed is a tuple,
                        -- replace [x] by its known value.
                        opt info $ subs x (vals !! n) c
                    _ ->
                        CAccess n v x $ opt info c
            _ -> CAccess n v x $ opt info c
        opt info (CSwitch (VInt n) clist def) =
          -- If the value by compared is known at compile time,
          -- just access the expected branch.
          case List.lookup n clist of
            Just c -> opt info c
            Nothing -> opt info def
        opt info (CSwitch v clist def) =
          CSwitch v (List.map (\(n,c) -> (n, opt info c)) clist) $ opt info def
        opt info c = c
    in
    List.foldl (\c n ->
      opt (gather IMap.empty c) c) c [1..n]



-- | Check the scope of the variables of the continuation expression.
check_cexpr :: [Variable] -> CExpr -> QpState ()
check_cexpr scope (CFun g arg body c) = do
  let nscope = List.union scope arg
  check_cexpr nscope body
  check_cexpr (g:scope) c
check_cexpr scope (CTailApp f arg) = do
  check_value scope f
  List.foldl (\rec a -> do
        rec
        check_value scope a) (return ()) arg
check_cexpr scope (CApp f arg x c) = do
  check_value scope f
  List.foldl (\rec a -> do
        rec
        check_value scope a) (return ()) arg
  check_cexpr (x:scope) c
check_cexpr scope (CTuple vals x c) = do
  List.foldl (\rec v -> do
        rec
        check_value scope v) (return ()) vals
  check_cexpr (x:scope) c
check_cexpr scope (CAccess n v x c) = do
  check_value scope v
  check_cexpr (x:scope) c
check_cexpr scope (CSwitch v clist c) = do
  check_value scope v
  List.foldl (\rec (_,c) -> do
        rec
        check_cexpr scope c) (return ()) clist
  check_cexpr scope c
check_cexpr scope (CRet v) =
  check_value scope v
check_cexpr scope (CSet x v) =
  check_value scope v
check_cexpr scope (CFree v c) = do
  check_value scope v
  check_cexpr scope c
check_cexpr scope (CError msg) =
  return ()


-- | Check the scope of the variables of a compile unit.
check_cunit :: CUnit -> QpState ()
check_cunit cu = do
  let scope = List.map (\(f,_,_) -> f) (local cu) ++ List.map (\(f,_,_) -> f) (extern cu) ++ List.map fst (vglobals cu)
  List.foldl (\rec (_, arg, c) -> do
        rec
        check_cexpr (List.union arg scope) c) (return ()) (local cu ++ extern cu)
  case main cu of
    Just c -> check_cexpr scope c
    Nothing -> return ()

-- | Pretty-print a value using Hughes's and Peyton Jones's
-- pretty printer combinators. The type 'Doc' is defined in the library
-- "Text.PrettyPrint.HughesPJ" and allows for nested documents.
print_value :: (Variable -> String)  -- ^ Rendering of term variables.
            -> Value                 -- ^ Expression to print.
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
           -> (Variable, [Variable], CExpr)             -- ^ Function to print.
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
            -> CExpr                 -- ^ Expression to print.
            -> Doc                   -- ^ Resulting PP document.
print_cexpr _ fvar (CApp f args x c) =
  let pargs = List.map (print_value fvar) args
      sargs = punctuate comma pargs in
  text (fvar x) <+> text ":=" <+> print_value fvar f <> text "(" <> hsep sargs <> text ");" $$
  print_cexpr Inf fvar c
print_cexpr _ fvar (CTailApp f args) =
  let pargs = List.map (print_value fvar) args
      sargs = punctuate comma pargs in
  print_value fvar f <> text "(" <> hsep sargs <> text ");"
print_cexpr _ fvar (CTuple vals x c) =
  let pvals = List.map (print_value fvar) vals
      svals = punctuate comma pvals in
  text (fvar x ++ " := [") <> hsep svals <> text "];" $$
  print_cexpr Inf fvar c
print_cexpr _ fvar (CAccess n x y c) =
  text (fvar y ++ " :=") <+> print_value fvar x <> text ("[" ++ show n ++ "];") $$
  print_cexpr Inf fvar c
print_cexpr _ fvar (CSwitch v clist def) =
  let pcs = List.map (\(n,c) -> (n,print_cexpr Inf fvar c)) clist
      pdef = text "default:" $$ nest 2 (print_cexpr Inf fvar def) in
  text "switch" <+> print_value fvar v <+> text "with" $$
  nest 2 (List.foldl (\doc (tag, c) ->
        doc $$
        text (show tag ++ ":") $$
        nest 2 c) empty pcs $$ pdef)
print_cexpr _ fvar (CFun f arg cf c) =
  print_cfun fvar (f, arg, cf) $$
  print_cexpr Inf fvar c
print_cexpr _ fvar (CSet x v) =
  text (fvar x) <+> text ":=" <+> print_value fvar v
print_cexpr _ fvar (CRet v) =
  text "ret" <+> print_value fvar v
print_cexpr _ fvar (CFree v c) =
  text "free" <+> print_value fvar v <> text ";" $$
  print_cexpr Inf fvar c
print_cexpr _ fvar (CError msg) =
  text "error \"" <> text msg <> text "\""


instance PPrint CExpr where
  -- Generic printing
  genprint lv [fvar] e =
    let doc = print_cexpr lv fvar e in
    PP.render doc
  genprint lv _ e =
    throwNE $ ProgramError "CPS:genprint(CExpr): illegal argument"

  -- Other
  -- By default, the term variables are printed as x_n and the data constructors as D_n,
  -- where n is the id of the variable / constructor
  sprintn lv e = genprint lv [prevar "%"] e



instance PPrint CUnit where
  genprint _ [fvar] cu =
    let pcfuns = List.map (print_cfun fvar) (extern cu ++ local cu) in
    let (gdef, ginit) = List.unzip $ List.map (\(g, e) ->
          (text (fvar g), print_cexpr Inf fvar e)) (vglobals cu) in
    let pimport = List.map (\v -> case v of
          VLabel x -> text $ fvar x
          VGlobal x -> text $ fvar x
          _ -> text "WATWATWAT") (imports cu) in
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
    throwNE $ ProgramError "CPS:genprint(CUnit): illegal argument"

  sprintn lv e = genprint lv [prevar "%"] e


