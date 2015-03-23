-- | This module provides functions that manipulate constraint sets, for the most part to reduce them.
module Typing.Subtyping where

import Classes
import Utils

import Core.Syntax
import Core.Printer

import Monad.Typer
import Monad.Error

import qualified Data.List as List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap

-- | Check whether a given flag constraint is trivial.
non_trivial :: Flag -> Flag -> Bool
non_trivial m n =
  (m /= n && n /= 1 && m /= 0)



-- | Using the type specifications registered in the state monad, unfold any subtyping
-- constraints of the form  (user /a/ \<: user /a/'). This functions assumes that the two type
-- names are the same, and that the correct number of arguments has been given.
unfold_algebraic_constraint :: Algebraic -> [Type] -> [Type] -> Typer ConstraintSet
unfold_algebraic_constraint utyp arg arg' = do
  -- Retrieve the specification of the type
  typedef <- algebraic_def utyp

  -- Build the constraints based on the variance of the type arguments
  let cset = List.foldl (\cset (var, a, a') ->
        case var of
          Covariant -> [a <: a'] <> cset
          Contravariant -> [a' <: a] <> cset
          Equal -> [a <: a', a' <: a] <> cset
          Unrelated -> cset
        ) emptyset $ List.zip3 (arguments typedef) arg arg'

  -- Return the complete set
  return cset




-- | Reduce the composite constraints of a constraint set, leaving only atomic
-- and semi-composite constraints.
break_composite :: ConstraintSet -> QpState ConstraintSet

-- Nothing to do
break_composite ([], lc) = return ([], lc)

-- Subtype constraints
break_composite ((Subtype (TypeAnnot n t) (TypeAnnot m (TypeApply "qubit" [])) info):lc, fc) = do
  unset_flag n info
  unset_flag m info
  break_composite ((SubLinearType t (TypeApply "qubit" []) info):lc, fc)

break_composite ((Subtype (TypeAnnot n (TypeApply "qubit" [])) (TypeAnnot m t) info):lc, fc) = do
  unset_flag n info
  unset_flag m info
  break_composite ((SubLinearType (TypeApply "qubit" []) t info):lc, fc)

break_composite ((Subtype (TypeAnnot _ (TypeApply c args)) (TypeAnnot _ (TypeApply c' args')) info):lc, fc) = do
  if c == c' && List.length args == List.length args' then
    break_composite (lc, fc)

  else
    throw_TypingError (TypeAnnot 0 (TypeApply c args)) (TypeAnnot 0 (TypeApply c' args')) info

break_composite ((Subtype (TypeAnnot _ TBool) (TypeAnnot _ TBool) _):lc, fc) = do
  break_composite (lc, fc)

break_composite ((Subtype (TypeAnnot _ TInt) (TypeAnnot _ TInt) _):lc, fc) = do
  break_composite (lc, fc)

break_composite ((Subtype (TypeAnnot _ t@(TCirc _ _)) (TypeAnnot _ u@(TCirc _ _)) info):lc, fc) = do
  break_composite ((SubLinearType t u info):lc, fc)

-- Unit against unit : removed
break_composite ((SubLinearType TUnit TUnit _):lc, fc) = do
  break_composite (lc, fc)


-- Bool against bool : removed
break_composite ((SubLinearType TBool TBool _):lc, fc) = do
  break_composite (lc, fc)


-- Int against int : removed
break_composite ((SubLinearType TInt TInt _):lc, fc) = do
  break_composite (lc, fc)

-- Qubit against QBit : removed
break_composite ((SubLinearType TQubit TQubit _):lc, fc) = do
  break_composite (lc, fc)


-- Arrow against arrow
  -- T -> U <: T' -> U'
-- Into
  -- T' <: T && U <: U'
break_composite ((SubLinearType (TArrow t u) (TArrow t' u') info):lc, fc) = do
  intype <- case c_type info of
              Just a -> return $ Just a
              Nothing -> return $ Just $ if c_actual info then TypeAnnot 0 $ TArrow t u else TypeAnnot 0 $ TArrow t' u'

  break_composite ((Subtype t' t info { c_actual = not $ c_actual info,
                                           c_type = intype }):
                      (Subtype u u' info { c_type = intype }):lc, fc)


-- Tensor against tensor
  -- T * U <: T' * U'
-- Into
  -- T <: T' && U <: U'
break_composite ((SubLinearType (TTensor tlist) (TTensor tlist') info):lc, fc) = do
  if List.length tlist == List.length tlist' then do
    intype <- case c_type info of
                Just a -> return $ Just a
                Nothing -> return $ Just $ if c_actual info then TypeAnnot 0 $ TTensor tlist else TypeAnnot 0 $ TTensor tlist'

    comp <- return $ List.map (\(t, u) -> Subtype t u info { c_type = intype }) $ List.zip tlist tlist'
    break_composite (comp ++ lc, fc)

  else do
    throw_TypingError (TypeAnnot 0 $ TTensor tlist) (TypeAnnot 0 $ TTensor tlist') info


-- With type synonyms
break_composite ((SubLinearType (TSynonym utyp arg) u info):lc, fc) = do
  spec <- synonym_def utyp

  let (arg', typ) = definition spec
  let typ' = List.foldl (\typ (a, a') -> do
        case (a, a') of
          (TypeAnnot n (TypeVar a), TypeAnnot n' a') -> subs a a' (subs n n' typ)
          _ -> throwNE $ ProgramError "Subtyping:break_composite: inadequate type arguments in type synonym definition") typ (List.zip arg' arg)

  break_composite ((SubLinearType (no_bang typ') u info):lc, fc)

break_composite ((SubLinearType t (TSynonym utyp arg) info):lc, fc) = do
  spec <- synonym_def utyp

  let (arg', typ) = definition spec
  let typ' = List.foldl (\typ (a, a') -> do
        case (a, a') of
          (TypeAnnot n (TypeVar a), TypeAnnot n' a') -> subs a a' (subs n n' typ)
          _ -> throwNE $ ProgramError "Subtyping:break_composite: inadequate type arguments in type synonym definition") typ (List.zip arg' arg)

  break_composite ((SubLinearType t (no_bang typ') info):lc, fc)


-- Algebraic type against algebraic type
-- The result of breaking this kind of constraints has been placed in the specification of the user type
-- It need only be instantiated with the current type arguments
break_composite ((SubLinearType (TAlgebraic utyp arg) (TAlgebraic utyp' arg') info):lc, fc) = do
  -- If the two types are the same (either two type synonyms or two algebraic types)
  if utyp == utyp' then do
    intype <- case c_type info of
          Just a -> return $ Just a
          Nothing -> return $ Just $ if c_actual info then TypeAnnot 0 $ TAlgebraic utyp arg else TypeAnnot 0 $ TAlgebraic utyp' arg'

    cset <- unfold_algebraic_constraint utyp arg arg'

    -- This one may be reversed : will have to check
    break_composite $ (cset & info { c_type = intype }) <> (lc, fc)
  else
    throw_TypingError (TypeAnnot 0 $ TAlgebraic utyp arg) (TypeAnnot 0 $ TAlgebraic utyp' arg') info


-- Circ against Circ
  -- circ (T, U) <: circ (T', U')
-- Into
  -- T' <: T && U <: U'
-- The flags don't really matter, as they can take any value, so no constraint m <= n is generated
break_composite ((SubLinearType (TCirc t u) (TCirc t' u') info):lc, fc) = do
  intype <- case c_type info of
              Just a -> return $ Just a
              Nothing -> return $ Just $ if c_actual info then TypeAnnot 0 $ TCirc t u else TypeAnnot 0 $ TCirc t' u'

  break_composite ((Subtype t' t info { c_actual = not $ c_actual info,
                                           c_type = intype }):(Subtype u u' info):lc, fc)


-- Semi composite (unbreakable) constraints
break_composite (c@(SubLinearType (TypeVar _) _ _):lc, fc) = do
  (lc', fc') <- break_composite (lc, fc)
  return (c:lc', fc')

break_composite (c@(SubLinearType _ (TypeVar _) _):lc, fc) = do
  (lc', fc') <- break_composite (lc, fc)
  return (c:lc', fc')

break_composite ((Subtype (TypeAnnot n a) (TypeAnnot m b) info):lc, fc) = do
  if non_trivial m n then do
    intype <- case c_type info of
                Nothing -> return $ Just $ if c_actual info then TypeAnnot n a else TypeAnnot m b
                Just a -> return $ Just a
    break_composite ((SubLinearType a b info):lc, (Le m n info):fc)
  else do
    break_composite ((SubLinearType a b info):lc, fc)


-- Everything else is a typing error
break_composite ((SubLinearType t u info):lc, fc) = do
  throw_TypingError (TypeAnnot 0 t) (TypeAnnot 0 u) info






