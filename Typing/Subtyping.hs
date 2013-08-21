-- | This module provides functions that manipulate constraint sets, for the most part to reduce them. 
module Typing.Subtyping where

import Classes

import Typing.CoreSyntax
import Typing.CorePrinter

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
unfold_user_constraint :: Variable -> [Type] -> Variable -> [Type] -> QpState ConstraintSet
unfold_user_constraint utyp arg utyp' arg' = do
  -- Retrieve the specification of the type
  Left spec <- type_spec utyp
  -- The constraints
  (a, a', cset) <- return $ d_subtype spec

  -- Replace the arguments a by arg
  cset <- List.foldl (\rec (TBang n (TVar x), TBang m b) -> do
                        cs <- rec
                        cset <- return $ subs_flag n m cs
                        return $ subs_typ_var x b cset) (return cset) (List.zip a arg)
  -- Replace the arguments a' by arg'
  cset <- List.foldl (\rec (TBang n (TVar x), TBang m b) -> do
                        cs <- rec
                        cset <- return $ subs_flag n m cs
                        return $ subs_typ_var x b cset) (return cset) (List.zip a' arg')

  return cset



-- | Apply the function 'unfold_user_constraints' to the constraints in a constraint set.
unfold_user_constraints_in_set :: ConstraintSet -> QpState ConstraintSet
unfold_user_constraints_in_set ([], fc) = return ([], fc)

unfold_user_constraints_in_set ((Sublintype (TUser utyp args) (TUser utyp' args') _):lc, fc) = do
  cset <- unfold_user_constraint utyp args utyp' args'
  cset' <- unfold_user_constraints_in_set (lc, fc)
  return $ cset <> cset'

unfold_user_constraints_in_set (c:lc, fc) = do
  (lc', fc') <- unfold_user_constraints_in_set (lc, fc)
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
  intype <- case in_type info of
              Just a -> return $ Just a
              Nothing -> return $ Just $ if actual info then TBang 0 $ TArrow t u else TBang 0 $ TArrow t' u'

  break_composite bu ((Subtype t' t info { actual = not $ actual info,
                                           in_type = intype }):
                      (Subtype u u' info { in_type = intype }):lc, fc)
 

-- Tensor against tensor
  -- T * U <: T' * U'
-- Into
  -- T <: T' && U <: U'
break_composite bu ((Sublintype (TTensor tlist) (TTensor tlist') info):lc, fc) = do
  if List.length tlist == List.length tlist' then do
    intype <- case in_type info of
                Just a -> return $ Just a
                Nothing -> return $ Just $ if actual info then TBang 0 $ TTensor tlist else TBang 0 $ TTensor tlist'

    comp <- return $ List.map (\(t, u) -> Subtype t u info { in_type = intype }) $ List.zip tlist tlist'
    break_composite bu (comp ++ lc, fc)

  else do
    throw_TypingError (TBang 0 $ TTensor tlist) (TBang 0 $ TTensor tlist') info


-- User type against user type
-- The result of breaking this kind of constraints has been placed in the specification of the user type
-- It need only be instantiated with the current type arguments
break_composite bu ((Sublintype (TUser utyp arg) (TUser utyp' arg') info):lc, fc) = do
  if utyp == utyp' then do
    
    if bu then do
      intype <- case in_type info of
                  Just a -> return $ Just a
                  Nothing -> return $ Just $ if actual info then TBang 0 $ TUser utyp arg else TBang 0 $ TUser utyp' arg'

      cset <- unfold_user_constraint utyp arg utyp' arg'

      -- This one may be reversed : will have to check
      break_composite bu $ (cset & info { in_type = intype }) <> (lc, fc)

    else do
      cset <- break_composite bu (lc, fc)
      return $ [Sublintype (TUser utyp arg) (TUser utyp' arg') info] <> cset
      
  else
    throw_TypingError (TBang 0 $ TUser utyp arg) (TBang 0 $ TUser utyp' arg') info


-- Circ against Circ
  -- circ (T, U) <: circ (T', U')
-- Into
  -- T' <: T && U <: U'
-- The flags don't really matter, as they can take any value, so no constraint m <= n is generated
break_composite bu ((Sublintype (TCirc t u) (TCirc t' u') info):lc, fc) = do
  intype <- case in_type info of
              Just a -> return $ Just a
              Nothing -> return $ Just $ if actual info then TBang 0 $ TCirc t u else TBang 0 $ TCirc t' u'

  break_composite bu ((Subtype t' t info { actual = not $ actual info,
                                           in_type = intype }):(Subtype u u' info):lc, fc)


-- Semi composite (unbreakable) constraints
break_composite bu (c@(Sublintype (TVar _) _ _):lc, fc) = do
  (lc', fc') <- break_composite bu (lc, fc)
  return (c:lc', fc')

break_composite bu (c@(Sublintype _ (TVar _) _):lc, fc) = do
  (lc', fc') <- break_composite bu (lc, fc)
  return (c:lc', fc')

break_composite bu ((Subtype (TBang n a) (TBang m b) info):lc, fc) = do
  if non_trivial n m then do
    intype <- case in_type info of
                Nothing -> return $ Just $ if actual info then TBang n a else TBang m b
                Just a -> return $ Just a
    break_composite bu ((Sublintype a b info):lc, (Le m n info):fc)
  else
    break_composite bu ((Sublintype a b info):lc, fc)


-- Everything else is a typing error
break_composite bu ((Sublintype t u info):lc, fc) = do
  throw_TypingError (TBang 0 t) (TBang 0 u) info






