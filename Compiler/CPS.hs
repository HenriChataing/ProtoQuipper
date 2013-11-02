{- This module contains the conversion from the pattern-less proto quipper to Continuation Passing Style. -}
module Compiler.CPS where

import Utils

import Monad.QpState

import qualified Compiler.SimplSyntax as S
import Compiler.QLib

import qualified Data.List as List


-- | The definition of values.
data Value =
    VVar Variable
  | VInt Int
  | VLabel Variable
  deriving (Show, Eq)

data AccessPath =
    Offset Int
  | Select Int AccessPath


-- | Definition of continuations.
data CExpr =
    CFun Variable [Variable] CExpr CExpr          -- ^ Function abstraction: @fun x1 .. xN -> t@.
  | CApp Value [Value]                            -- ^ Function application: @t u@.
  | CTuple [Value] Variable CExpr                 -- ^ Tuple: @(/t/1, .. , /t//n/)@. By construction, must have /n/ >= 2.
  | COffset Int Value Variable CExpr              -- ^ Return the pointer increased by an offset /n/.
  | CAccess Int Value Variable CExpr              -- ^ Access the nth element of a tuple.
  | CSwitch Value [CExpr]                         -- ^ Switch condition.
  | CPrimop [Value] (Maybe Variable) CExpr        -- ^ Primitive call. The arguments are given by the second argument, the return value is stored in the third. After
                                                  -- that, the continuation c is called.
  deriving Show



-- | Replace a variable by a value into a continuation expression.
replace :: Variable -> Value -> CExpr -> CExpr
replace x v (CFun f arg e e') =
  CFun f arg (replace x v e) (replace x v e')
replace x v (CApp f arg) =
  let f' = rep_val x v f
      arg' = List.map (rep_val x v) arg in
  CApp f' arg'
replace x v (CTuple vlist y e) =
  let vlist' = List.map (rep_val x v) vlist in
  CTuple vlist' y (replace x v e)
replace x v (CAccess n w y e) =
  CAccess n (rep_val x v w) y (replace x v e)
replace x v (CSwitch w elist) =
  CSwitch (rep_val x v w) (List.map (replace x v) elist)
replace x v e = e

-- | Application of the function replace to a single value.
rep_val x v (VVar y) | x == y = v
                     | otherwise = VVar y
rep_val _ _ v = v


-- | Convert an expression from the simplified syntax to the continuation passing style.
convert_to_cps :: (Value -> QpState CExpr)        -- ^ A continuation.
               -> S.Expr                          -- ^ Argument expression.
               -> QpState CExpr                   -- ^ The resulting continuation expression.

convert_to_cps c (S.EVar v) =
  c (VVar v)

convert_to_cps c (S.EGlobal v) =
  c (VVar v)

convert_to_cps c (S.EInt n) =
  c (VInt n)

convert_to_cps c (S.EBool b) =
  c (if b then VInt 1 else VInt 0)

convert_to_cps c S.EUnit =
  c (VInt 0)

convert_to_cps c (S.ETuple []) =
  c (VInt 0)

convert_to_cps c (S.ETuple elist) = do
  x <- dummy_var
  aux elist (\w -> do
        cx <- c (VVar x)
        return $ CTuple w x cx)
  where
    aux l c = do
      let aux' [] w = c (List.reverse w)
          aux' (e:es) w = convert_to_cps (\v -> aux' es (v:w)) e
      aux' l []

convert_to_cps c (S.EAccess n x) = do
  y <- dummy_var
  cy <- c (VVar y)
  return $ CAccess n (VVar x) y cy
  
convert_to_cps c (S.EFun x e) = do
  f <- dummy_var       -- function name
  k <- dummy_var       -- continuation argument
  -- At the end of the body, the result is passed to the continuation k
  body <- convert_to_cps (\z -> return $ CApp (VVar k) [z]) e 
  -- The reference f of the function is passed to the building continuation c
  cf <- c (VVar f)
  return $ CFun f [x, k] body $ cf

convert_to_cps c (S.ERecFun f x e) = do
  k <- dummy_var       -- continuation argument
  -- At the end of the body, the result is passed to the continuation k
  body <- convert_to_cps (\z -> return $ CApp (VVar k) [z]) e 
  -- The reference f of the function is passed to the building continuation c
  cf <- c (VVar f)
  return $ CFun f [x, k] body $ cf

convert_to_cps c (S.EApp e f) = do
  r <- dummy_var       -- return address
  x <- dummy_var       -- argument of the return address
  app <- convert_to_cps (\f -> convert_to_cps (\e -> return $ CApp f [e, VVar r]) e) f
  cx <- c (VVar x)
  return $ CFun r [x] cx app

convert_to_cps c (S.ESeq e f) = do
  convert_to_cps (\z -> convert_to_cps c f) e

convert_to_cps c (S.ELet x e f) = do
  convert_to_cps (\z -> do
        cf <- convert_to_cps c f
        return $ replace x z cf) e

convert_to_cps c (S.EIf e f g) = do
  k <- dummy_var
  x <- dummy_var
  cx <- c (VVar x)
  f' <- convert_to_cps (\z -> return $ CApp (VVar k) [z]) f
  g' <- convert_to_cps (\z -> return $ CApp (VVar k) [z]) g
  convert_to_cps (\e ->
        return $ CFun k [x] cx $
                 CSwitch e [g', f']) e

convert_to_cps c (S.EMatch e blist) = do
  k <- dummy_var
  x <- dummy_var
  cx <- c (VVar x)
  let slist = List.sortBy (\(n,_) (m,_) -> compare n m) blist
  elist' <- List.foldl (\rec (_, e) -> do
        es <- rec
        e' <- convert_to_cps (\z -> return $ CApp (VVar k) [z]) e
        return $ e':es) (return []) slist
  convert_to_cps (\e ->
        return $ CFun k [x] cx $
                 CSwitch e (List.reverse elist')) e

convert_to_cps c (S.EBuiltin s) =
  c (VInt 0)


-- | Convert the toplevel declarations into the CPS form.
convert_declarations :: (Value -> QpState CExpr)   -- ^ Semantic continuation.
                     -> [S.Declaration]            -- ^ List of declarations.
                     -> QpState CExpr              -- ^ Resulting continuationj expression.
convert_declarations c decls = do
  List.foldr (\d rec -> do
        ce <- rec
        case d of
          S.DExpr e -> do
              convert_to_cps (\_ -> return ce) e
          
          S.DLet x e -> do
              r <- dummy_var
              convert_to_cps (\z ->
                    return $ CFun r [x] ce $
                             CApp (VVar r) [z]) e
    ) (c $ VInt 0) decls
