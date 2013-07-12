module TransSyntax (translate_program, translate_type) where

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



-- | Import the type definitions in the current state
-- The data constructors are labelled during this operation, and included in the field datacons of the state
-- User types are added the same, with an id set to -1 to distinguish them from other type variables
import_typedefs :: [S.Typedef] -> QpState (Map String Int)
import_typedefs typedefs = do
  -- Import the names of the types in the current labelling map
  -- This operation permits the writing of inductive types
  m <- List.foldl (\rec (S.Typedef typename _ _) -> do
                     m <- rec
                     return $ Map.insert typename (-1) m) (return Map.empty) typedefs

  -- Transcribe the rest of the type definitions
  List.foldl (\rec (S.Typedef typename _ dlist) -> do
                m <- rec
                List.foldl (\rec (dcon, dtype) -> do
                              m <- rec
                              dtype' <- translate_type_with_label dtype m
                              id <- register_datacon dcon typename dtype'
                              return $ Map.insert dcon id m) (return m) dlist) (return m) typedefs 


-- | Translate a type, given a labelling
translate_type_with_label :: S.Type -> Map String Int -> QpState Type
translate_type_with_label S.TUnit _ = do
  return $ TBang (-1) TUnit

translate_type_with_label S.TBool _ = do
  return $ TBang (-1) TBool

translate_type_with_label S.TQBit _ = do
  return $ TBang 0 TQbit

translate_type_with_label (S.TVar x) label = do
  case Map.lookup x label of
    Just (-1) ->
        return $ TBang (-1) (TUser x)

    Just id ->
        return $ TBang (-1) (TVar id)

    Nothing ->
        -- This could be a user defined type : need to add a check
        fail ("Unbound type variable: " ++ x)

translate_type_with_label (S.TArrow t u) label = do
  t' <- translate_type_with_label t label
  u' <- translate_type_with_label u label
  return $ TBang (-2) (TArrow t' u')

translate_type_with_label (S.TTensor tlist) label = do
  tlist' <- List.foldr (\t rec -> do
                          r <- rec
                          t' <- translate_type_with_label t label
                          return (t':r)) (return []) tlist
  return $ TBang (-2) (TTensor tlist')

translate_type_with_label (S.TBang t) label = do
  TBang _ t' <- translate_type_with_label t label
  return $ TBang 1 t'

translate_type_with_label (S.TCirc t u) label = do
  t' <- translate_type_with_label t label
  u' <- translate_type_with_label u label
  return $ TBang (-1) (TCirc t' u')

translate_type_with_label (S.TLocated t _) label = do
  translate_type_with_label t label


-- | Same as the translate function above, but with an empty labelling map
translate_type :: S.Type -> QpState Type
translate_type t =
  translate_type_with_label t Map.empty


-- | Translate a pattern, given a labelling
-- The map is updated, as the variables are bound in the pattern
translate_pattern_with_label :: S.Pattern -> Map String Int -> QpState (Pattern, Map String Int)
translate_pattern_with_label S.PUnit label = do
  return (PUnit, label)

translate_pattern_with_label (S.PVar x) label = do
  id <- register_var x
  return (PVar id, Map.insert x id label)

translate_pattern_with_label (S.PTuple plist) label = do
  (plist', lbl) <- List.foldr (\p rec -> do
                                  (r, lbl) <- rec
                                  (p', lbl') <- translate_pattern_with_label p lbl
                                  return ((p':r), lbl')) (return ([], label)) plist
  return (PTuple plist', lbl)

translate_pattern_with_label (S.PData datacon p) label = do
  case Map.lookup datacon label of
    Just id -> do
        (p', lbl) <- translate_pattern_with_label p label
        return (PData id p', lbl)

    Nothing -> do
        ex <- get_location
        throw $ UnboundDatacon datacon ex

translate_pattern_with_label (S.PLocated p ex) label = do
  set_location ex
  (p', lbl) <- translate_pattern_with_label p label
  return (PLocated p' ex, lbl)


-- | Translate an expression, given a labelling map
translate_expression_with_label :: S.Expr -> Map String Int -> QpState Expr
translate_expression_with_label S.EUnit _ = do
  return EUnit

translate_expression_with_label (S.EBool b) _ = do
  return (EBool b)

translate_expression_with_label (S.EVar x) label = do
  case Map.lookup x label of
    Just id ->
        return (EVar id)

    Nothing -> do
        ex <- get_location
        throw $ UnboundVariable x ex

translate_expression_with_label (S.EFun p e) label = do
  (p', lbl) <- translate_pattern_with_label p label
  e' <- translate_expression_with_label e lbl
  return (EFun p' e')

translate_expression_with_label (S.ELet p e f) label = do
  e' <- translate_expression_with_label e label
  (p', lbl) <- translate_pattern_with_label p label
  f' <- translate_expression_with_label f lbl
  return (ELet p' e' f')

translate_expression_with_label (S.EData datacon e) label = do
  case Map.lookup datacon label of
    Just id -> do
        e' <- translate_expression_with_label e label
        return (EData id e')

    Nothing -> do
        ex <- get_location
        throw $ UnboundDatacon datacon ex

translate_expression_with_label (S.EMatch e blist) label = do
  e' <- translate_expression_with_label e label
  blist' <- List.foldr (\(p, f) rec -> do
                          r <- rec
                          (p', lbl) <- translate_pattern_with_label p label
                          f' <- translate_expression_with_label f lbl
                          return ((p', f'):r)) (return []) blist
  return (EMatch e' blist')

translate_expression_with_label (S.EApp e f) label = do
  e' <- translate_expression_with_label e label
  f' <- translate_expression_with_label f label
  return (EApp e' f')

translate_expression_with_label (S.ETuple elist) label = do
  elist' <- List.foldr (\e rec -> do
                          r <- rec
                          e' <- translate_expression_with_label e label
                          return (e':r)) (return []) elist
  return (ETuple elist')

translate_expression_with_label (S.EIf e f g) label = do
  e' <- translate_expression_with_label e label
  f' <- translate_expression_with_label f label
  g' <- translate_expression_with_label g label
  return (EIf e' f' g')

translate_expression_with_label (S.EBox t) _ = do
  t' <- translate_type t
  return (EBox t')

translate_expression_with_label S.EUnbox _ = do
  return EUnbox

translate_expression_with_label S.ERev _ = do
  return ERev

translate_expression_with_label (S.ELocated e ex) label = do
  set_location ex
  e' <- translate_expression_with_label e label
  return $ ELocated e' ex


-- Label the gates
import_gates :: QpState (Map String Int)
import_gates = do
  li0 <- register_var "INIT0"
  li1 <- register_var "INIT1"
  ti0 <- register_var "TERM0"
  ti1 <- register_var "TERM1"

  m <- return $ Map.fromList [("INIT0", li0), ("INIT1", li1), ("TERM0", ti0), ("TERM1", ti1)]

  m' <- List.foldl (\rec g -> do
                      m <- rec
                      id <- register_var g
                      return $ Map.insert g id m) (return m) unary_gates
  
  List.foldl (\rec g -> do
                m <- rec
                id <- register_var g
                return $ Map.insert g id m) (return m') binary_gates


-- | Translate a whole program
-- Proceeds in three steps:
--   Import the type definitions
--   Import the gates
--   Translate the expression body
translate_program :: ([S.Typedef], S.Expr) -> QpState Expr
translate_program (typedefs, body) = do
  dcons <- import_typedefs typedefs

  gates <- import_gates
  ctx <- get_context
  set_context $ ctx { gatesid = gates }

  translate_expression_with_label body (Map.union dcons gates)


