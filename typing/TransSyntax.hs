module TransSyntax where

import CoreSyntax
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

safe_find :: String -> State Int
safe_find s = State (\bc -> case Map.lookup s $ bindings bc of
                              Just n -> (bc, n)
                              Nothing -> (bc { var_id = (+1) $ var_id bc,
                                               names = Map.insert (var_id bc) s $ names bc,
                                               bindings = Map.insert s (var_id bc) $ bindings bc }, var_id bc))

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

translate_type :: S.Type -> State Type
--------------------------------------
translate_type (S.TVar x) = do
  n <- safe_find x
  return $ TVar n

translate_type (S.TArrow t u) = do
  t' <- translate_type t
  u' <- translate_type u
  return $ TArrow t' u'

translate_type (S.TTensor t u) = do
  t' <- translate_type t
  u' <- translate_type u
  return $ TTensor t' u'

translate_type (S.TExp t) = do
  t' <- translate_type t
  return $ TExp 1 t'

translate_type (S.TLocated t _) = do
  translate_type t


-- Translation of patterns
translate_pattern :: S.Pattern -> State Pattern
-----------------------------------------------
translate_pattern S.PUnit = do
  return PUnit

translate_pattern (S.PVar v) = do
  x <- label v
  return (PVar x)

translate_pattern (S.PPair p q) =  do
  p' <- translate_pattern p
  q' <- translate_pattern q
  return (PPair p' q')


-- Translation of expressions
translate_expression :: S.Expr -> State Expr
--------------------------------------------
translate_expression S.EUnit = do
  return EUnit

translate_expression (S.EVar v) = do
  x <- find v
  return (EVar x)

translate_expression (S.EFun p e) = do
  set_mark
  p' <- translate_pattern p
  e' <- translate_expression e
  reset
  return (EFun p' e')

translate_expression (S.ELet p e f) = do
  set_mark
  p' <- translate_pattern p
  e' <- translate_expression e
  f' <- translate_expression f
  reset
  return (ELet p' e' f')

translate_expression (S.EApp e f) = do
  e' <- translate_expression e
  f' <- translate_expression f
  return (EApp e' f')

translate_expression (S.EPair e f) = do
  e' <- translate_expression e
  f' <- translate_expression f
  return (EPair e' f')

