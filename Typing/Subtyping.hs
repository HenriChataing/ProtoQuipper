-- | This module provides functions that manipulate constraint sets, for the most part to reduce them.
module Typing.Subtyping where

import Classes
import Utils

import Core.Syntax
import Core.Printer

import Monad.QuipperError
import Monad.QpState

import qualified Data.List as List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap

-- | Check whether a given flag constraint is trivial.
non_trivial :: RefFlag -> RefFlag -> Bool
non_trivial m n =
  (m /= n && n /= 1 && m /= 0)



-- | Using the type specifications registered in the state monad, unfold any subtyping
-- constraints of the form  (user /a/ \<: user /a/'). This functions assumes that the two type
-- names are the same, and that the correct number of arguments has been given.
unfold_algebraic_constraint :: Algebraic -> [Type] -> Algebraic -> [Type] -> QpState ConstraintSet
unfold_algebraic_constraint utyp arg utyp' arg' = do
  -- Retrieve the specification of the type
  spec <- algebraic_def utyp
  -- The constraints
  let (a, a', cset) = d_subtype spec

  -- Replace the arguments a by arg
  let cset' = List.foldl (\cset (TBang n t, TBang m b) ->
        let x = unTVar t in
        subs_flag n m (subs_typ_var x b cset)) cset $ List.zip a arg
  -- Replace the arguments a' by arg'
  let cset'' = List.foldl (\cset (TBang n t, TBang m b) -> do
        let x = unTVar t
        subs_flag n m (subs_typ_var x b cset)) cset' $ List.zip a' arg'

  return cset''
    where
      unTVar (TVar x) = x
      unTVar _ = throwNE $ ProgramError "Subtyping:unfold_algebraic_constraint: unexpected non-atomic constraint"


-- | Apply the function 'unfold_algebraic_constraints' to the constraints in a constraint set.
unfold_algebraic_constraints_in_set :: ConstraintSet -> QpState ConstraintSet
unfold_algebraic_constraints_in_set ([], fc) = return ([], fc)

unfold_algebraic_constraints_in_set ((Sublintype (TAlgebraic utyp args) (TAlgebraic utyp' args') _):lc, fc) = do
  cset <- unfold_algebraic_constraint utyp args utyp' args'
  cset' <- unfold_algebraic_constraints_in_set (lc, fc)
  return $ cset <> cset'

unfold_algebraic_constraints_in_set (c:lc, fc) = do
  (lc', fc') <- unfold_algebraic_constraints_in_set (lc, fc)
  return (c:lc', fc')



-- | Reduce the composite constraints of a constraint set, leaving only atomic
-- and semi-composite constraints. The boolean argument indicates whether to break user
-- type constraints or not. When this flag is set, the user type constraints are left untouched:
-- this is useful for the extension of the subtyping relations to algebraic types, where one wants
-- to reduce only the non-algebraic type constraints.
break_composite :: Bool -> ConstraintSet -> QpState ConstraintSet

-- Nothing to do
break_composite bu ([], lc) = return ([], lc)

-- Subtype constraints
break_composite bu ((Subtype (TBang n t) (TBang m TQubit) info):lc, fc) = do
  unset_flag n info
  unset_flag m info
  break_composite bu ((Sublintype t TQubit info):lc, fc)

break_composite bu ((Subtype (TBang n TQubit) (TBang m t) info):lc, fc) = do
  unset_flag n info
  unset_flag m info
  break_composite bu ((Sublintype TQubit t info):lc, fc)

break_composite bu ((Subtype (TBang _ TUnit) (TBang _ TUnit) _):lc, fc) = do
  break_composite bu (lc, fc)

break_composite bu ((Subtype (TBang _ TBool) (TBang _ TBool) _):lc, fc) = do
  break_composite bu (lc, fc)

break_composite bu ((Subtype (TBang _ TInt) (TBang _ TInt) _):lc, fc) = do
  break_composite bu (lc, fc)

break_composite bu ((Subtype (TBang _ t@(TCirc _ _)) (TBang _ u@(TCirc _ _)) info):lc, fc) = do
  break_composite bu ((Sublintype t u info):lc, fc)

-- Unit against unit : removed
break_composite bu ((Sublintype TUnit TUnit _):lc, fc) = do
  break_composite bu (lc, fc)


-- Bool against bool : removed
break_composite bu ((Sublintype TBool TBool _):lc, fc) = do
  break_composite bu (lc, fc)


-- Int against int : removed
break_composite bu ((Sublintype TInt TInt _):lc, fc) = do
  break_composite bu (lc, fc)

-- Qubit against QBit : removed
break_composite bu ((Sublintype TQubit TQubit _):lc, fc) = do
  break_composite bu (lc, fc)


-- Arrow against arrow
  -- T -> U <: T' -> U'
-- Into
  -- T' <: T && U <: U'
break_composite bu ((Sublintype (TArrow t u) (TArrow t' u') info):lc, fc) = do
  intype <- case c_type info of
              Just a -> return $ Just a
              Nothing -> return $ Just $ if c_actual info then TBang 0 $ TArrow t u else TBang 0 $ TArrow t' u'

  break_composite bu ((Subtype t' t info { c_actual = not $ c_actual info,
                                           c_type = intype }):
                      (Subtype u u' info { c_type = intype }):lc, fc)


-- Tensor against tensor
  -- T * U <: T' * U'
-- Into
  -- T <: T' && U <: U'
break_composite bu ((Sublintype (TTensor tlist) (TTensor tlist') info):lc, fc) = do
  if List.length tlist == List.length tlist' then do
    intype <- case c_type info of
                Just a -> return $ Just a
                Nothing -> return $ Just $ if c_actual info then TBang 0 $ TTensor tlist else TBang 0 $ TTensor tlist'

    comp <- return $ List.map (\(t, u) -> Subtype t u info { c_type = intype }) $ List.zip tlist tlist'
    break_composite bu (comp ++ lc, fc)

  else do
    throw_TypingError (TBang 0 $ TTensor tlist) (TBang 0 $ TTensor tlist') info


-- With type synonyms
break_composite bu ((Sublintype (TSynonym utyp arg) u info):lc, fc) = do
  spec <- synonym_def utyp

  let (arg', typ) = s_unfolded spec
  let typ' = List.foldl (\typ (a, a') -> do
        case (a, a') of
          (TBang n (TVar a), TBang n' a') -> subs_typ_var a a' (subs_flag n n' typ)
          _ -> throwNE $ ProgramError "Subtyping:break_composite: inadequate type arguments in type synonym definition") typ (List.zip arg' arg)

  break_composite bu ((Sublintype (no_bang typ') u info):lc, fc)

break_composite bu ((Sublintype t (TSynonym utyp arg) info):lc, fc) = do
  spec <- synonym_def utyp

  let (arg', typ) = s_unfolded spec
  let typ' = List.foldl (\typ (a, a') -> do
        case (a, a') of
          (TBang n (TVar a), TBang n' a') -> subs_typ_var a a' (subs_flag n n' typ)
          _ -> throwNE $ ProgramError "Subtyping:break_composite: inadequate type arguments in type synonym definition") typ (List.zip arg' arg)

  break_composite bu ((Sublintype t (no_bang typ') info):lc, fc)


-- Algebraic type against algebraic type
-- The result of breaking this kind of constraints has been placed in the specification of the user type
-- It need only be instantiated with the current type arguments
break_composite bu ((Sublintype (TAlgebraic utyp arg) (TAlgebraic utyp' arg') info):lc, fc) = do
  -- If the two types are the same (either two type synonyms or two algebraic types)
  if utyp == utyp' then do

    if bu then do
      intype <- case c_type info of
                  Just a -> return $ Just a
                  Nothing -> return $ Just $ if c_actual info then TBang 0 $ TAlgebraic utyp arg else TBang 0 $ TAlgebraic utyp' arg'

      cset <- unfold_algebraic_constraint utyp arg utyp' arg'

      -- This one may be reversed : will have to check
      break_composite bu $ (cset & info { c_type = intype }) <> (lc, fc)

    else do
      cset <- break_composite bu (lc, fc)
      return $ [Sublintype (TAlgebraic utyp arg) (TAlgebraic utyp' arg') info] <> cset

  else
    throw_TypingError (TBang 0 $ TAlgebraic utyp arg) (TBang 0 $ TAlgebraic utyp' arg') info


-- Circ against Circ
  -- circ (T, U) <: circ (T', U')
-- Into
  -- T' <: T && U <: U'
-- The flags don't really matter, as they can take any value, so no constraint m <= n is generated
break_composite bu ((Sublintype (TCirc t u) (TCirc t' u') info):lc, fc) = do
  intype <- case c_type info of
              Just a -> return $ Just a
              Nothing -> return $ Just $ if c_actual info then TBang 0 $ TCirc t u else TBang 0 $ TCirc t' u'

  break_composite bu ((Subtype t' t info { c_actual = not $ c_actual info,
                                           c_type = intype }):(Subtype u u' info):lc, fc)


-- Semi composite (unbreakable) constraints
break_composite bu (c@(Sublintype (TVar _) _ _):lc, fc) = do
  (lc', fc') <- break_composite bu (lc, fc)
  return (c:lc', fc')

break_composite bu (c@(Sublintype _ (TVar _) _):lc, fc) = do
  (lc', fc') <- break_composite bu (lc, fc)
  return (c:lc', fc')

break_composite bu ((Subtype (TBang n a) (TBang m b) info):lc, fc) = do
  if non_trivial m n then do
    intype <- case c_type info of
                Nothing -> return $ Just $ if c_actual info then TBang n a else TBang m b
                Just a -> return $ Just a
    break_composite bu ((Sublintype a b info):lc, (Le m n info):fc)
  else do
    break_composite bu ((Sublintype a b info):lc, fc)


-- Everything else is a typing error
break_composite bu ((Sublintype t u info):lc, fc) = do
  throw_TypingError (TBang 0 t) (TBang 0 u) info






