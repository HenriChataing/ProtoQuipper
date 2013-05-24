module CTransCore where

import CCoreSyntax
import qualified Syntax as S

import Data.Map as Map



data BindingContext =
  Ctx {
    bindings :: Map String Int,
    names :: Map Int String,
    var_id :: Int,
    mark :: [Map String Int] -- Screenshot of the bindings at some point
  }
newtype State a = State (BindingContext -> (BindingContext, a))

instance Monad State where
  return a = State (\bc -> (bc, a))
  State run >>= action = State (\bc -> let (bc', a) = run bc in
                                       let State run' = action a in
                                       run' bc')

label :: String -> State Int
label s = State (\bc -> (bc { var_id = (+1) $ var_id bc,
                              bindings = Map.insert s (var_id bc) $ bindings bc,
                              names = Map.insert (var_id bc) s $ names bc }, var_id bc))

find :: String -> State Int
find s = State (\bc -> (bc, case Map.lookup s $ bindings bc of
                              Just x -> x
                              Nothing -> error ("Unbound variable" ++ s)))

set_mark :: State ()
set_mark = State (\bc -> (bc { mark = (bindings bc):(mark bc) }, ()))

reset :: State ()
reset = State (\bc -> case mark bc of
                        [] -> error "Cannot reset the bindings, no mark taken"
                        m:mc -> (bc { bindings = m, mark = mc }, ()))

empty_context :: BindingContext
empty_context =
  Ctx {
    bindings = empty,
    names = empty,
    var_id = 0,
    mark = []
  }

--------------------------------------
-- Translation into internal Syntax --

-- Translation of expressions
translateExpr :: S.Expr -> State Expr
-----------------------------------------------------
translateExpr S.EUnit = do
  return EUnit

translateExpr (S.EVar v) = do
  x <- find v
  return (EVar x)

translateExpr (S.EFun (S.PVar v) e) = do
  set_mark
  x <- label v
  e' <- translateExpr e
  reset
  return (EFun x e')

translateExpr (S.ELet (S.PPair (S.PVar u) (S.PVar v)) e f) = do
  set_mark
  x <- label u
  y <- label v
  e' <- translateExpr e
  f' <- translateExpr f
  reset
  return (ELet x y e' f')

translateExpr (S.EApp e f) = do
  e' <- translateExpr e
  f' <- translateExpr f
  return (EApp e' f')

translateExpr (S.EPair e f) = do
  e' <- translateExpr e
  f' <- translateExpr f
  return (EPair e' f')

