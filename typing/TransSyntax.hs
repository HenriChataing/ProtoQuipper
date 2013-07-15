module TransSyntax (translate_program, translate_type) where

import Utils
import Classes
import Localizing
import QuipperError

import CoreSyntax
import CorePrinter

import qualified Syntax as S
import Printer

import QpState

import Gates

import Control.Exception

import Data.Map as Map
import qualified Data.List as List



-- | Import the type definitions in the current state
-- The data constructors are labelled during this operation, and included in the field datacons of the state
-- User types are added the same, with an id set to -1 to distinguish them from other type variables
import_typedefs :: [S.Typedef] -> QpState (Map String Int)
import_typedefs typedefs = do
  -- Import the names of the types in the current labelling map
  -- This operation permits the writing of inductive types
  m <- List.foldl (\rec (S.Typedef typename args _) -> do
                     m <- rec
                     n <- fresh_flag
                     register_type typename $ List.length args
                     return $ Map.insert typename (TBang n $ TUser typename []) m) (return Map.empty) typedefs

  -- Transcribe the rest of the type definitions
  -- Type definitions include : the name of the type, generic variables, the list of constructors
  List.foldl (\rec (S.Typedef typename args dlist) -> do
                lbl <- rec

                -- Bind the arguments of the type
                -- For each string argument a, a type !n a is created and bound
                (args', m') <- List.foldr (\a rec -> do
                                             (args, m) <- rec
                                             id <- register_var a
                                             n <- fresh_flag
                                             ta <- return $ TBang n (TVar id)
                                             return (ta:args, Map.insert a ta m)) (return ([], m)) args

                -- Define the type of the data constructors
                List.foldl (\rec (dcon, dtype) -> do
                              lbl <- rec
                              (dtype', cset) <- case dtype of
                                                  -- If the constructor takes no argument
                                                  Nothing -> do
                                                      n <- fresh_flag 
                                                      return (TBang n (TUser typename args'), emptyset)

                                                  -- If the constructor takes an argument
                                                  Just dt -> do
                                                      (dt'@(TBang n _), cset) <- translate_type dt [] m'
                                                      return (TBang anyflag (TArrow dt' (TBang n $ TUser typename args')), cset)

                              -- Generalize the type of the constructor over the free variables an types
                              (fv, ff) <- return (free_var dtype', free_flag dtype')
                              dtype' <- return $ TForall fv ff cset dtype'

                              -- Register the datacon
                              id <- register_datacon dcon typename dtype'
                              return $ Map.insert dcon id lbl) (return lbl) dlist) (return Map.empty) typedefs 


-- | Translate a type, given a labelling.
-- The arguments of type applications are passed via the function calls
-- The output includes a set of structural constraints : eg !p (!n a * !m b) imposes p <= n and p <= m
translate_type :: S.Type -> [Type] -> Map String Type -> QpState (Type, ConstraintSet)
translate_type S.TUnit [] _ = do
  return (TBang anyflag TUnit, emptyset)

translate_type S.TBool [] _ = do
  return (TBang anyflag TBool, emptyset)

translate_type S.TQBit [] _ = do
  return (TBang zero TQbit, emptyset)

translate_type (S.TVar x) args label = do
  case Map.lookup x label of
    -- This case corresponds to user types
    Just (TBang _ (TUser _ _)) -> do
        -- Expected number of args
        nexp <- type_def x
        -- Actual number of args
        nact <- return $ List.length args

        if nexp == nact then do
          n <- fresh_flag
          return (TBang n (TUser x args), emptyset)
        else do
          ex <- get_location
          throw $ WrongTypeArguments x nexp nact ex

    Just typ ->
        if args == [] then
          return (typ, emptyset)
        else do
          ex <- get_location
          throw $ WrongTypeArguments (pprint typ) 0 (List.length args) ex

    Nothing -> do
        ex <- get_location
        throw $ UnboundVariable x ex

translate_type (S.TArrow t u) [] label = do
  (t', csett) <- translate_type t [] label
  (u', csetu) <- translate_type u [] label
  n <- fresh_flag
  return (TBang n (TArrow t' u'), csett <> csetu)

translate_type (S.TTensor tlist) [] label = do
  n <- fresh_flag
  (tlist', cset') <- List.foldr (\t rec -> do
                                   (r, cs) <- rec
                                   (t'@(TBang m _), cs') <- translate_type t [] label
                                   return ((t':r), ([], [(n, m)]) <> cs' <> cs)) (return ([], emptyset)) tlist
  return (TBang n (TTensor tlist'), cset')

translate_type (S.TBang t) [] label = do
  (t'@(TBang n _), cset) <- translate_type t [] label
  set_flag n
  return (t', cset)

translate_type (S.TCirc t u) [] label = do
  (t', csett) <- translate_type t [] label
  (u', csetu) <- translate_type u [] label
  return (TBang anyflag (TCirc t' u'), csett <> csetu)

-- Case of type application : the argument is pushed onto the arg list
translate_type (S.TApp t u) args label = do
  (u', cset) <- translate_type u [] label
  (t', cset') <- translate_type t (u':args) label
  return (t', cset <> cset')

translate_type (S.TLocated t ex) args label = do
  set_location ex
  translate_type t args label

-- Remaining cases : of types applied to an argument when they are not generic
translate_type t args label = do
  ex <- get_location
  throw $ WrongTypeArguments (pprint t) 0 (List.length args) ex



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

translate_pattern_with_label (S.PDatacon datacon p) label = do
  case Map.lookup datacon label of
    Just id -> do
        case p of
          Just p -> do
              (p', lbl) <- translate_pattern_with_label p label
              return (PDatacon id (Just p'), lbl)

          Nothing ->
              return (PDatacon id Nothing, label)

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

translate_expression_with_label (S.EDatacon datacon e) label = do
  case Map.lookup datacon label of
    Just id -> do
        case e of
          Just e -> do
              e' <- translate_expression_with_label e label
              return (EDatacon id $ Just e')

          Nothing ->
              return (EDatacon id Nothing)

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
  (t', _) <- translate_type t [] Map.empty
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
translate_program :: S.Program -> QpState Expr
translate_program prog = do
  dcons <- import_typedefs $ S.typedefs prog

  gates <- import_gates
  ctx <- get_context
  set_context $ ctx { gatesid = gates }

  translate_expression_with_label (S.body prog) (Map.union dcons gates)


