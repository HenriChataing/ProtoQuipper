module TransSyntax (translate_type, translate_pattern, translate_expression,
                    label, label_gates, find_name) where

import Utils
import Localizing
import QuipperError

import CoreSyntax
import qualified Syntax as S

import QpState

import Gates

import Control.Exception

import Data.Map as Map
import qualified Data.List as List


{-
  Complement to the functions defined in the Contexts module :
  A set of functions dedicated to the labelling of variables,
  and the bindings manipulation :

  - label : create a new variable id, and bind the name in the context (current layer)
  - find_name : retrieves the id associated with a name, if the name can't be found, an scope error is generated
  - find : same as find_name, only if the name isn't found in the context, a new label is created

  And for the layer manipulation :
  - new_layer : creates an new empty layer
  - drop_layer : removes the top layer and all its bindings

  Some additional functions manipulate type ids instead of variable ids :
  - label_type : same as label, instead generates a type id
  - find_tyep : same as find_name, but never fails, if the name isn't found, a new id is generated
-}

dummy_label :: QpState Int
label :: String -> QpState Int
label_type :: String -> QpState Int
find_name :: String -> QpState Int
find_type :: String -> QpState Int

new_layer :: QpState ()
drop_layer :: QpState ()
----------------------
dummy_label = QpState (\ctx -> return (ctx { var_id = (+1) $ var_id ctx }, var_id ctx))

label s = QpState (\ctx -> case name_to_var ctx of
                           [] ->
                               return (ctx { var_id = (+1) $ var_id ctx,
                                             name_to_var = [ Map.singleton s (var_id ctx) ],
                                             var_to_name = Map.insert (var_id ctx) s $ var_to_name ctx }, var_id ctx)
                           toplayer:rest -> 
                               return (ctx { var_id = (+1) $ var_id ctx,
                                             name_to_var = (Map.insert s (var_id ctx) toplayer):rest,
                                             var_to_name = Map.insert (var_id ctx) s $ var_to_name ctx }, var_id ctx))

label_type s = QpState (\ctx -> case name_to_var ctx of
                           [] ->
                               return (ctx { type_id = (+1) $ type_id ctx,
                                             name_to_var = [ Map.singleton s (type_id ctx) ] }, type_id ctx)
                           toplayer:rest -> 
                               return (ctx { var_id = (+1) $ var_id ctx,
                                             name_to_var = (Map.insert s (var_id ctx) toplayer):rest }, type_id ctx))

-- Auxiliary function that looks for the variable in the successive layers
find_rec :: String -> [Map.Map String Int] -> Maybe Int
find_rec _ [] = Nothing
find_rec s (top:rest) =
  case Map.lookup s top of
    Just x -> Just x
    Nothing -> find_rec s rest

find_name s = QpState (\ctx ->
                      case find_rec s $ name_to_var ctx of
                        Just x -> return (ctx, x)
                        Nothing -> throw $ UnboundVariable s extent_unknown)

find_type s = QpState (\ctx ->
                      case find_rec s $ name_to_var ctx of
                        Just x -> return (ctx, x)
                        Nothing -> let QpState run = label_type s in
                                   run ctx)


new_layer =
  QpState (\ctx -> return (ctx { name_to_var = Map.empty:(name_to_var ctx) }, ()))

drop_layer =
  QpState (\ctx -> return (ctx { name_to_var = case name_to_var ctx of
                                               [] -> []
                                               _:rest -> rest }, ()))



{-
  Translation from surface syntax to core syntax, three functions provided :
 
  - translate_type
  - translate_pattern
  - translate_expression

  which do as their name indicates
-}

translate_type :: S.Type -> QpState Type
translate_pattern :: S.Pattern -> QpState Pattern
translate_expression :: S.Expr -> QpState Expr
-------------------------------------------
translate_type S.TUnit = do
  return $ TExp (-1) (TUnit, NoInfo)

translate_type S.TBool = do
  return $ TExp (-1) (TBool, NoInfo)

translate_type S.TQBit = do
  return $ TExp 0 (TQbit, NoInfo)

translate_type (S.TVar x) = do
  n <- find_type x
  return $ TExp 0 (TVar n, NoInfo)

translate_type (S.TArrow t u) = do
  t' <- translate_type t
  u' <- translate_type u
  return $ TExp 0 (TArrow t' u', NoInfo)

translate_type (S.TTensor tlist) = do
  tlist' <- List.foldr (\t rec -> do
                          r <- rec
                          t' <- translate_type t
                          return (t':r)) (return []) tlist
  return $ TExp 0 (TTensor tlist', NoInfo)

translate_type (S.TSum t u) = do
  t' <- translate_type t
  u' <- translate_type u
  return $ TExp 0 (TSum t' u', NoInfo)

translate_type (S.TExp t) = do
  TExp _ t' <- translate_type t
  return $ TExp 1 t'

translate_type (S.TCirc t u) = do
  t' <- translate_type t
  u' <- translate_type u
  return $ TExp (-1) (TCirc t' u', NoInfo)

translate_type (S.TLocated t _) = do
  translate_type t

------------------------------
translate_pattern S.PUnit = do
  return PUnit

translate_pattern (S.PVar v) = do
  x <- label v
  return (PVar x)

translate_pattern (S.PTuple plist) =  do
  plist' <- List.foldr (\p rec -> do
                          r <- rec
                          p' <- translate_pattern p
                          return (p':r)) (return []) plist
  return (PTuple plist')

translate_pattern (S.PLocated p ex) = do
  p' <- translate_pattern p
  return (PLocated p' ex)

---------------------------------
-- Secifically translate a pattern matching
translate_match x ((p, f):plist) = do
  new_layer
  p' <- translate_pattern p
  f' <- translate_expression f
  drop_layer
  case plist of
    [(q, g)] -> do
        new_layer
        q' <- translate_pattern q
        g' <- translate_expression g
        drop_layer
        return (EMatch x (p', f') (q', g'))
    _ -> do
        y <- dummy_label
        m <- translate_match (EVar y) plist
        return (EMatch x (p', f') (PVar y, m))

translate_expression S.EUnit = do
  return EUnit

translate_expression (S.EBool b) = do
  return $ EBool b

translate_expression (S.EVar v) = do
  x <- find_name v
  return (EVar x)

translate_expression (S.EFun p e) = do
  new_layer
  p' <- translate_pattern p
  e' <- translate_expression e
  drop_layer
  return (EFun p' e')

translate_expression (S.ELet p e f) = do
  e' <- translate_expression e
  new_layer
  p' <- translate_pattern p
  f' <- translate_expression f
  drop_layer
  return (ELet p' e' f')

translate_expression (S.EInjL e) = do
  e' <- translate_expression e
  return (EInjL e')

translate_expression (S.EInjR e) = do
  e' <- translate_expression e
  return (EInjR e')

translate_expression (S.EMatch e ((p, f):plist)) = do
  e' <- translate_expression e
  new_layer
  p' <- translate_pattern p
  f' <- translate_expression f
  drop_layer
  case plist of
    [(q, g)] -> do
        new_layer
        q' <- translate_pattern q
        g' <- translate_expression g
        drop_layer
        return (EMatch e' (p', f') (q', g'))
    _ -> do
        x <- dummy_label
        m <- translate_match (EVar x) plist
        return (EMatch e' (p', f') (PVar x, m))

translate_expression (S.EApp e f) = do
  e' <- translate_expression e
  f' <- translate_expression f
  return (EApp e' f')

translate_expression (S.ETuple elist) = do
  elist' <- List.foldr (\e rec -> do
                          r <- rec
                          e' <- translate_expression e
                          return (e':r)) (return []) elist
  return (ETuple elist')

translate_expression (S.EIf e f g) = do
  e' <- translate_expression e
  f' <- translate_expression f
  g' <- translate_expression g
  return $ EIf e' f' g'

translate_expression (S.EBox t) = do
  t' <- translate_type t
  return $ EBox t'

translate_expression S.EUnbox = do
  return $ EUnbox

translate_expression S.ERev = do
  return ERev

translate_expression (S.ELocated e ex) = do
  e' <- translate_expression e
  return $ ELocated e' ex


-- Label the gates
label_gates :: QpState ()
label_gates = do
  _ <- label "INIT0"
  _ <- label "INIT1"
  _ <- label "TERM0"
  _ <- label "TERM1"

  List.foldl (\rec g -> do
                rec
                _ <- label g
                return ()) (return ()) unary_gates
  
  List.foldl (\rec g -> do
                rec
                _ <- label g
                return ()) (return ()) binary_gates


