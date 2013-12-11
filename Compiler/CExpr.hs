-- | This module contains the definition of the last language used before the cnstruction of the LLVM module.
-- It explicitates the flow control, and uses only simple operations.
module Compiler.CExpr where

import Prelude hiding (lookup)

import Utils
import Classes hiding ((<+>))

import Monad.QpState
import Monad.QuipperError

import qualified Typing.CoreSyntax as CS

import qualified Compiler.SimplSyntax as S
import Compiler.Circ
import Compiler.Interfaces

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


-- | Are considered free variables only variables bound in a local scope.
instance Param Value where
  free_var (VVar x) = [x]
  free_var _ = []

  subs_var _ _ v = v


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
  | CSwitch Value [CExpr]                          -- ^ Switch condition.
  | CRet Value                                     -- ^ Return a value. This instruction is terminal.
  | CSet Variable Value                            -- ^ This instruction is terminal, and specific to global variables, where it is necessary to set a specific variable.
  deriving Show



instance Param CExpr where
  free_var (CFun f args cf c) =
    List.union (free_var cf List.\\ args) (free_var c List.\\ [f])
  free_var (CApp f args x c) =
    List.foldl (\fv a ->
          List.union (free_var a) fv) (free_var c List.\\ [x]) (f:args)
  free_var (CTailApp f args) =
    List.foldl (\fv a ->
          List.union (free_var a) fv) [] (f:args)
  free_var (CTuple vlist x c) =
    let fvl = List.foldl (\fv a ->
          List.union (free_var a) fv) [] vlist in
    List.union (free_var c List.\\ [x]) fvl
  free_var (CAccess _ v x c) =
    List.union (free_var c List.\\ [x]) (free_var v)
  free_var (CSwitch v clist) =
    List.foldl (\fv c ->
          List.union (free_var c) fv) (free_var v) clist
  free_var (CSet x v) = free_var v
  free_var (CRet v) = free_var v

  subs_var _ _ c = c


-- | Compilation unit.
data CUnit = CUnit {
  imports :: [Value],                      -- ^ The list of functions and variables imported from extern modules.
  local :: [FunctionDef],
  extern :: [FunctionDef],
  vglobals :: [GlobalDef]                  -- ^ Contains the list of global variables, along with the code initializing these variables.
}


-- | The type of function declarations.
type FunctionDef = (Variable, [Variable], CExpr)

-- | The type of global variable declarations.
type GlobalDef = (Variable, CExpr)

-- | The type of conversion functions.
type Conversion = ((IQLib, IBuiltins) -> CContext -> (Value -> QpState CExpr) -> S.Expr -> QpState CExpr)


-- | Convert an expression from the simplified syntax to the continuation passing style.
convert_to_cps :: (IQLib, IBuiltins)              -- ^ Interfaces to the QLib and Builtins modules.
               -> CContext                        -- ^ Current context.
               -> (Value -> QpState CExpr)        -- ^ A continuation.
               -> S.Expr                          -- ^ Argument expression.
               -> QpState CExpr                   -- ^ The resulting continuation expression.

convert_to_cps dict vals c (S.EVar x) =
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

convert_to_cps dict vals c (S.EGlobal x) =
  convert_to_cps dict vals c (S.EVar x)

convert_to_cps dict vals c (S.EInt n) =
  c (VInt n)

convert_to_cps dict vals c (S.EBool b) =
  c (if b then VInt 1 else VInt 0)

convert_to_cps dict vals c S.EUnit =
  c (VInt 0)

convert_to_cps dict vals c (S.ETuple []) =
  c (VInt 0)

convert_to_cps dict vals c (S.ETuple elist) = do
  x <- create_var "x"
  aux elist (\w -> do
        cx <- c (VVar x)
        return $ CTuple w x cx)
  where
    aux l c = do
      let aux' [] w = c (List.reverse w)
          aux' (e:es) w = convert_to_cps dict vals (\v -> aux' es (v:w)) e
      aux' l []

convert_to_cps dict vals c (S.EAccess n x) = do
  y <- create_var "x"
  cy <- c (VVar y)
  return $ CAccess n (value vals x) y cy

convert_to_cps dict vals c (S.EFun x e) = do
  f <- create_var "f"       -- function name
  k <- create_var "k"       -- continuation argument
  -- At the end of the body, the result is passed to the continuation k
  body <- convert_to_cps dict vals (\z -> return $ CTailApp (VVar k) [z]) e
  -- The reference f of the function is passed to the building continuation c
  cf <- c (VVar f)
  return $ CFun f [x, k] body $ cf

convert_to_cps dict vals c (S.ERecFun f x e) = do
  k <- create_var "k"       -- continuation argument
  -- At the end of the body, the result is passed to the continuation k
  let vals' = IMap.insert f (VVar f) vals
  body <- convert_to_cps dict vals' (\z -> return $ CTailApp (VVar k) [z]) e
  -- The reference f of the function is passed to the building continuation c
  cf <- c (VVar f)
  return $ CFun f [x, k] body $ cf

-- the direct application of global functions is treated separately.
convert_to_cps dict vals c (S.EApp (S.EVar f) arg) = do
  r <- create_var "r"       -- return address
  x <- create_var "x"       -- argument of the return address
  case value vals f of
    VLabel f -> do
        app <- convert_to_cps dict vals (\arg ->
              return $ CTailApp (VLabel f) [arg, VVar r]) arg
        cx <- c (VVar x)
        return $ CFun r [x] cx app
    _ -> do
        app <- convert_to_cps dict vals (\f ->
              convert_to_cps dict vals (\arg ->
              return $ CTailApp f [arg, VVar r]) arg) (S.EVar f)
        cx <- c (VVar x)
        return $ CFun r [x] cx app

convert_to_cps dict vals c (S.EApp (S.EGlobal f) arg) =
  convert_to_cps dict vals c (S.EApp (S.EVar f) arg)

convert_to_cps dict vals c (S.EApp f arg) = do
  r <- create_var "r"       -- return address
  x <- create_var "x"       -- argument of the return address
  app <- convert_to_cps dict vals (\f ->
        convert_to_cps dict vals (\arg ->
              return $ CTailApp f [arg, VVar r]) arg) f
  cx <- c (VVar x)
  return $ CFun r [x] cx app

convert_to_cps dict vals c (S.ESeq e f) = do
  convert_to_cps dict vals (\z -> convert_to_cps dict vals c f) e

convert_to_cps dict vals c (S.ELet x e f) = do
  convert_to_cps dict vals (\z -> do
        convert_to_cps dict (IMap.insert x z vals) c f) e

convert_to_cps dict vals c (S.EIf e f g) = do
  k <- create_var "k"
  x <- create_var "x"
  cx <- c (VVar x)
  f' <- convert_to_cps dict vals (\z -> return $ CTailApp (VVar k) [z]) f
  g' <- convert_to_cps dict vals (\z -> return $ CTailApp (VVar k) [z]) g
  convert_to_cps dict vals (\e ->
        return $ CFun k [x] cx $
                 CSwitch e [g', f']) e

convert_to_cps dict vals c (S.EMatch e blist) = do
  k <- create_var "k"
  x <- create_var "x"
  cx <- c (VVar x)
  let slist = List.sortBy (\(n,_) (m,_) -> compare n m) blist
  elist' <- List.foldl (\rec (_, e) -> do
        es <- rec
        e' <- convert_to_cps dict vals (\z -> return $ CTailApp (VVar k) [z]) e
        return $ e':es) (return []) slist
  convert_to_cps dict vals (\e ->
        return $ CFun k [x] cx $
                 CSwitch e (List.reverse elist')) e

convert_to_cps (iqlib, ibuiltins) vals c (S.EBuiltin s) =
  case lookup s iqlib of
    Just v -> c (VGlobal v)
    Nothing ->
        case lookup s ibuiltins of
          Just v -> c (VGlobal v)
          Nothing -> fail $ "CPS:convert_to_cps: undefined builtin operation: " ++ s



-- | Convert an expression from the simplified syntax to a weak form of the continuation passing style, where only branching conditions impose the use of continuations.
convert_to_wcps :: (IQLib, IBuiltins)             -- ^ Interfaces to the QLib and Builtins modules.
               -> CContext                        -- ^ Current context.
               -> (Value -> QpState CExpr)        -- ^ A continuation.
               -> S.Expr                          -- ^ Argument expression.
               -> QpState CExpr                   -- ^ The resulting continuation expression.
convert_to_wcps dict vals c (S.EVar x) =
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

convert_to_wcps dict vals c (S.EGlobal x) =
  convert_to_wcps dict vals c (S.EVar x)

convert_to_wcps dict vals c (S.EInt n) =
  c (VInt n)

convert_to_wcps dict vals c (S.EBool b) =
  c (if b then VInt 1 else VInt 0)

convert_to_wcps dict vals c S.EUnit =
  c (VInt 0)

convert_to_wcps dict vals c (S.ETuple []) =
  c (VInt 0)

convert_to_wcps dict vals c (S.ETuple elist) = do
  x <- create_var "x"
  aux elist (\w -> do
        cx <- c (VVar x)
        return $ CTuple w x cx)
  where
    aux l c = do
      let aux' [] w = c (List.reverse w)
          aux' (e:es) w = convert_to_wcps dict vals (\v -> aux' es (v:w)) e
      aux' l []

convert_to_wcps dict vals c (S.EAccess n x) = do
  y <- create_var "x"
  cy <- c (VVar y)
  return $ CAccess n (value vals x) y cy

convert_to_wcps dict vals c (S.EFun x e) = do
  f <- create_var "f"       -- function name
  -- At the end of the body, the result is returned using CRet
  body <- convert_to_wcps dict vals (\z -> return $ CRet z) e
  -- The reference f of the function is passed to the building continuation c
  cf <- c (VVar f)
  return $ CFun f [x] body $ cf

convert_to_wcps dict vals c (S.ERecFun f x e) = do
  -- At the end of the body, the result is returned using CRet k
  let vals' = IMap.insert f (VVar f) vals
  body <- convert_to_wcps dict vals' (\z -> return $ CRet z) e
  -- The reference f of the function is passed to the building continuation c
  cf <- c (VVar f)
  return $ CFun f [x] body $ cf

-- the direct application of global functions is treated separately.
convert_to_wcps dict vals c (S.EApp (S.EVar f) arg) = do
  x <- create_var "x"    -- result of the application
  case value vals f of
    VLabel f -> do
        cx <- c (VVar x)
        convert_to_wcps dict vals (\arg ->
              return $ CApp (VLabel f) [arg] x cx) arg
    _ -> do
        cx <- c (VVar x)
        convert_to_wcps dict vals (\f ->
              convert_to_wcps dict vals (\arg ->
                    return $ CApp f [arg] x cx) arg) (S.EVar f)

convert_to_wcps dict vals c (S.EApp (S.EGlobal f) arg) =
  convert_to_wcps dict vals c (S.EApp (S.EVar f) arg)

convert_to_wcps dict vals c (S.EApp f arg) = do
  x <- create_var "x"       -- result of the application
  cx <- c (VVar x)
  convert_to_wcps dict vals (\f ->
        convert_to_wcps dict vals (\arg ->
              return $ CApp f [arg] x cx) arg) f

convert_to_wcps dict vals c (S.ESeq e f) = do
  convert_to_wcps dict vals (\z -> convert_to_wcps dict vals c f) e

convert_to_wcps dict vals c (S.ELet x e f) = do
  convert_to_wcps dict vals (\z -> do
        convert_to_wcps dict (IMap.insert x z vals) c f) e

convert_to_wcps dict vals c (S.EIf e f g) = do
  k <- create_var "k"
  x <- create_var "x"
  cx <- c (VVar x)
  f' <- convert_to_wcps dict vals (\z -> return $ CTailApp (VVar k) [z]) f
  g' <- convert_to_wcps dict vals (\z -> return $ CTailApp (VVar k) [z]) g
  convert_to_wcps dict vals (\e ->
        return $ CFun k [x] cx $
                 CSwitch e [g', f']) e

convert_to_wcps dict vals c (S.EMatch e blist) = do
  -- until a better solution is found, each branch finishes with a call to the function implementing the continuation
  k <- create_var "k"
  x <- create_var "x"
  cx <- c (VVar x)
  let slist = List.sortBy (\(n,_) (m,_) -> compare n m) blist
  elist' <- List.foldl (\rec (_, e) -> do
        es <- rec
        e' <- convert_to_wcps dict vals (\z -> return $ CTailApp (VVar k) [z]) e
        return $ e':es) (return []) slist
  convert_to_wcps dict vals (\e ->
        return $ CFun k [x] cx $
                 CSwitch e (List.reverse elist')) e

convert_to_wcps (iqlib, ibuiltins) vals c (S.EBuiltin s) =
  case lookup s iqlib of
    Just v -> c (VGlobal v)
    Nothing ->
        case lookup s ibuiltins of
          Just v -> c (VGlobal v)
          Nothing -> fail $ "CPS:convert_to_wcps: undefined builtin operation: " ++ s



-- | Convert the toplevel declarations into CPS form.
convert_declarations_to_cps :: (IQLib, IBuiltins)         -- ^ Interfaces to the QLib and Builtins modules.
                            -> [S.Declaration]            -- ^ List of declarations.
                            -> QpState CUnit              -- ^ Resulting compile unit.
convert_declarations_to_cps dict decls = do
  -- build the list of imported variables
  let imported = List.foldl (\imp (S.DLet _ e) -> List.union (S.imports e) imp) [] decls
  (ivals, imported) <- List.foldl (\rec ix -> do
        (ivals, imported) <- rec
        tix <- type_of_global ix
        if CS.is_fun tix then
          return (IMap.insert ix (VLabel ix) ivals, (VLabel ix):imported)
        else
          return (IMap.insert ix (VGlobal ix) ivals, (VGlobal ix):imported)) (return (IMap.empty, [])) imported

  -- translate the declarations
  (cu, _) <- List.foldl (\rec (S.DLet f e) -> do
        (cu, vals) <- rec
        case e of
          S.EFun x c -> do
              k <- create_var "k"       -- continuation argument
              fc <- create_var "fc"     -- closure argument
              body <- convert_to_cps dict vals (\z -> return $ CTailApp (VVar k) [z]) c
              (funs, body) <- closure_conversion body >>= return . lift_functions
              return (cu { local = funs ++ local cu, extern = (f, [fc,x,k], body):(extern cu) },
                      IMap.insert f (VLabel f) vals)

          S.ERecFun _ x c -> do
              k <- create_var "k"       -- continuation argument
              fc <- create_var "fc"     -- closure argument
              let vals' = IMap.insert f (VLabel f) vals
              body <- convert_to_cps dict vals' (\z -> return $ CTailApp (VVar k) [z]) c
              (funs, body) <- closure_conversion body >>= return . lift_functions
              return (cu { local = funs ++ local cu, extern = (f, [fc,x,k], body):(extern cu) }, vals')

          _ -> do
              -- translate the computation of g
              init <- convert_to_cps dict vals (\z -> return $ CSet f z) e
              (funs,init) <- closure_conversion init >>= return . lift_functions
              -- return the extend compile unit
              return (cu { local = funs ++ local cu, vglobals = (f, init):(vglobals cu) }, IMap.insert f (VGlobal f) vals)

    ) (return (CUnit { local = [], extern = [], vglobals = [], imports = imported}, ivals)) decls
  return cu { extern = List.reverse $ extern cu, vglobals = List.reverse $ vglobals cu }


-- | Convert the toplevel declarations into wCPS form.
convert_declarations_to_wcps :: (IQLib, IBuiltins)         -- ^ Interfaces to the QLib and Builtins modules.
                            -> [S.Declaration]            -- ^ List of declarations.
                            -> QpState CUnit              -- ^ Resulting compile unit.
convert_declarations_to_wcps dict decls = do
  -- build the list of imported variables
  let imported = List.foldl (\imp (S.DLet _ e) -> List.union (S.imports e) imp) [] decls
  (ivals, imported) <- List.foldl (\rec ix -> do
        (ivals, imported) <- rec
        tix <- type_of_global ix
        if CS.is_fun tix then
          return (IMap.insert ix (VLabel ix) ivals, (VLabel ix):imported)
        else
          return (IMap.insert ix (VGlobal ix) ivals, (VGlobal ix):imported)) (return (IMap.empty, [])) imported

  -- translate the declarations
  (cu, _) <- List.foldl (\rec (S.DLet f e) -> do
        (cu, vals) <- rec
        case e of
          S.EFun x c -> do
              fc <- create_var "fc"     -- closure argument
              body <- convert_to_wcps dict vals (\z -> return $ CRet z) c
              (funs, body) <- closure_conversion body >>= return . lift_functions
              return (cu { local = funs ++ local cu, extern = (f, [fc,x], body):(extern cu) },
                      IMap.insert f (VLabel f) vals)

          S.ERecFun _ x c -> do
              fc <- create_var "fc"     -- closure argument
              let vals' = IMap.insert f (VLabel f) vals
              body <- convert_to_wcps dict vals' (\z -> return $ CRet z) c
              (funs, body) <- closure_conversion body >>= return . lift_functions
              return (cu { local = funs ++ local cu, extern = (f, [fc,x], body):(extern cu) }, vals')

          _ -> do
              -- translate the computation of g
              init <- convert_to_wcps dict vals (\z -> return $ CSet f z) e
              (funs,init) <- closure_conversion init >>= return . lift_functions
              -- return the extend compile unit
              return (cu { local = funs ++ local cu, vglobals = (f, init):(vglobals cu) }, IMap.insert f (VGlobal f) vals)

    ) (return (CUnit { local = [], extern = [], vglobals = [], imports = imported}, ivals)) decls
  return cu { extern = List.reverse $ extern cu, vglobals = List.reverse $ vglobals cu }




-- | Closure conversion of the CPS code. This auxiliary function also returns the set of free variables of the produced expression.
closure_conversion_aux :: CExpr -> QpState (CExpr, [Variable])
closure_conversion_aux (CFun f args cf c) = do
  -- close the function body and continuation
  (cf', fvcf) <- closure_conversion_aux cf
  (c', fvc) <- closure_conversion_aux c

  -- free variables of f
  let fv = fvcf List.\\ args
  -- name of the function pointer and closure
  f' <- create_var "f"
  f'' <- create_var "fc"
  cl <- create_var "c"

  -- extraction of the free variables of cf'
  let cf'' = List.foldl (\cf (x,n) ->
        CAccess n (VVar f'') x cf) cf' $ List.zip fv [1..List.length fv]

  -- construction of the closure (with continuation c' and name f)
  let c'' = CTuple (VVar f':(List.map VVar fv)) f c'

  -- re-definition of the function f
  return (CFun f' (f'':args) cf'' c'', List.union fv (fvc List.\\ [f]))

closure_conversion_aux (CApp (VVar f) args x c) = do
  f' <- create_var "f"
  (c', fvc) <- closure_conversion_aux c
  return ( CAccess 0 (VVar f) f' $                     -- Extract the function pointer
           CApp (VVar f') (VVar f:args) x c',          -- Apply the function to its own closure
           List.union (fvc List.\\ [x]) (f:(List.concat $ List.map free_var args)) )

-- since global functions are already closed, only a dummy closure is passed as argument.
closure_conversion_aux (CApp (VLabel f) args x c) = do
  (c', fvc) <- closure_conversion_aux c
  return ( CApp (VLabel f) (VInt 0:args) x c',         -- Apply the function to a dummy closure (0)
           List.union (fvc List.\\ [x]) (List.concat $ List.map free_var args) )

closure_conversion_aux (CTailApp (VVar f) args) = do
  f' <- create_var "f"
  return ( CAccess 0 (VVar f) f' $                     -- Extract the function pointer
           CTailApp (VVar f') (VVar f:args),           -- Apply the function to its own closure
           f:(List.concat $ List.map free_var args) )

-- since global functions are already closed, only a dummy closure is passed as argument.
closure_conversion_aux (CTailApp (VLabel f) args) = do
  return ( CTailApp (VLabel f) (VInt 0:args),               -- Apply the function to a dummy closure (1)
           List.concat $ List.map free_var args )

closure_conversion_aux (CTuple vlist x c) = do
  (c', fvc) <- closure_conversion_aux c
  let fv = List.nub $ List.concat $ List.map free_var vlist
  return (CTuple vlist x c', List.union fv (fvc List.\\ [x]))

closure_conversion_aux (CAccess n v x c) = do
  (c', fvc) <- closure_conversion_aux c
  return (CAccess n v x c', List.union (free_var v) (fvc List.\\ [x]))

closure_conversion_aux (CSwitch v clist) = do
  (clist', fvc) <- List.foldl (\rec c -> do
        (cl, fvc) <- rec
        (c', fvc') <- closure_conversion_aux c
        return (c':cl, List.union fvc' fvc)) (return ([], [])) clist
  return (CSwitch v (List.reverse clist'), List.union (free_var v) fvc)

closure_conversion_aux e =
  return (e, free_var e)


-- | Closure conversion of the CPS code.
closure_conversion :: CExpr -> QpState CExpr
closure_conversion e = do
  (e, _) <- closure_conversion_aux e
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

lift_functions (CSwitch v clist) =
  let (funs, clist') = List.foldl (\(fs, cl) c ->
        let (fs', c') = lift_functions c in
        (fs' ++ fs, c':cl)) ([], []) clist in
  (funs, CSwitch v $ List.reverse clist')

lift_functions (CApp f args x c) =
  let (funs, c') = lift_functions c in
  (funs, CApp f args x c')

lift_functions c =
 ([], c)




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
print_cexpr _ fvar (CSwitch v clist) =
  let tags = [0 .. List.length clist-1]
      pcs = List.map (print_cexpr Inf fvar) clist in
  text "switch" <+> print_value fvar v <+> text "with" $$
  nest 2 (List.foldl (\doc (tag, c) ->
        doc $$
        text (show tag ++ ":") $$
        nest 2 c) empty (List.zip tags pcs))
print_cexpr _ fvar (CFun _ _ _ _) =
  text ""
print_cexpr _ fvar (CSet x v) =
  text (fvar x) <+> text ":=" <+> print_value fvar v
print_cexpr _ fvar (CRet v) =
  text "ret" <+> print_value fvar v


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

    let all =
          text "extern" <+> hsep (punctuate comma pimport) $$
          text "globals" <+> hsep (punctuate comma gdef) $$ text " " $$
          text "init () {" $$
          nest 2 (vcat ginit) $$
          text "}" $$
          text " " $$
          vcat pcfuns in
    PP.render all
  genprint _ _ _ =
    throwNE $ ProgramError "CPS:genprint(CUnit): illegal argument"

  sprintn lv e = genprint lv [prevar "%"] e


