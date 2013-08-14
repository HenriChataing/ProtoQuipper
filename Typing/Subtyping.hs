-- | This module provides functions that operate constraint sets: reduction mostly.
module Typing.Subtyping where

import Classes

import Typing.CoreSyntax
import Typing.CorePrinter

import Monad.QuipperError
import Monad.QpState

import qualified Data.List as List



-- | Using the type specifications registered in the state monad, unfolds any subtyping
-- constraints of the form  user a <: user a'. This functions assumes that the two type
-- names are the same, and that the right number of arguments has been given.
unfold_user_constraint :: String -> [Type] -> String -> [Type] -> QpState [TypeConstraint]
unfold_user_constraint utyp arg utyp' arg' = do
  -- Retrieve the specification of the type
  spec <- type_spec utyp
  -- The constraints
  (a, a', cset) <- return $ subtype spec

  -- Replace the arguments a by arg
  cset <- List.foldl (\rec (TBang n (TVar x), TBang m b) -> do
                        cs <- rec
                        cset <- return $ subs_flag n m ((cs, []) :: ConstraintSet)
                        return $ fst $ subs_typ_var x b cset) (return cset) (List.zip a arg)
  -- Replace the arguments a' by arg'
  cset <- List.foldl (\rec (TBang n (TVar x), TBang m b) -> do
                        cs <- rec
                        cset <- return $ subs_flag n m ((cs, []) :: ConstraintSet)
                        return $ fst $ subs_typ_var x b cset) (return cset) (List.zip a' arg')

  return cset




-- | Reduces the composite constrainst of a constraint set, leaving only atomic
-- and semi composite constraints. The boolean argument indicates whether to break user
-- type constraints or not. When this flag is set, the user type constraints are left untouched:
-- this is useful for the extension of the subtyping relations to algebraic types, where one wants
-- to reduce only the non-algebraic type constraints.
break_composite :: Bool -> ConstraintSet -> QpState ConstraintSet

-- Nothing to do
break_composite bu ([], lc) = return ([], lc)


-- Unit against unit : removed
break_composite bu ((Sublintype TUnit TUnit _):lc, fc) = do
  break_composite bu (lc, fc)


-- Bool against bool : removed
break_composite bu ((Sublintype TBool TBool _):lc, fc) = do
  break_composite bu (lc, fc)


-- Int against int : removed
break_composite bu ((Sublintype TInt TInt _):lc, fc) = do
  break_composite bu (lc, fc)


-- Qbit against QBit : removed
break_composite bu ((Sublintype TQbit TQbit _):lc, fc) = do
  break_composite bu (lc, fc)


-- Arrow against arrow
  -- T -> U <: T' -> U' 
-- Into
  -- T' <: T && U <: U'
break_composite bu ((Sublintype (TArrow t u) (TArrow t' u') info):lc, fc) = do
  break_composite bu ((Subtype t' t info { actual = not $ actual info }):(Subtype u u' info):lc, fc)
 

-- Tensor against tensor
  -- T * U <: T' * U'
-- Into
  -- T <: T' && U <: U'
break_composite bu ((Sublintype (TTensor tlist) (TTensor tlist') info):lc, fc) = do
  if List.length tlist == List.length tlist' then do
    comp <- return $ List.map (\(t, u) -> Subtype t u info) $ List.zip tlist tlist'
    break_composite bu (comp ++ lc, fc)

  else do
    fail ""
    throwQ $ TypingError (pprint $ TTensor tlist) (pprint $ TTensor tlist')
    -- throw_TypingError (TBang p (TTensor tlist)) (TBang q (TTensor tlist'))


-- User type against user type
-- The result of breaking this kind of constraints has been placed in the specification of the user type
-- It need only be instanciated with the current type arguments
break_composite bu ((Sublintype (TUser utyp arg) (TUser utyp' arg') info):lc, fc) = do
  if utyp == utyp' then do
    
    if bu then do
      cset <- unfold_user_constraint utyp arg utyp' arg'
      break_composite bu $ cset <> (lc, fc)

    else do
      cset <- break_composite bu (lc, fc)
      return $ [Sublintype (TUser utyp arg) (TUser utyp' arg') info] <> cset
      
  else
    throwQ $ TypingError (pprint (TUser utyp arg)) (pprint (TUser utyp' arg'))


-- Circ against Circ
  -- circ (T, U) <: circ (T', U')
-- Into
  -- T' <: T && U <: U'
-- The flags don't really matter, as they can take any value, so no constraint m <= n is generated
break_composite bu ((Sublintype (TCirc t u) (TCirc t' u') info):lc, fc) = do
  break_composite bu ((Subtype t' t info { actual = not $ actual info }):(Subtype u u' info):lc, fc)


-- Semi composite (unbreakable) constraints
break_composite bu (c@(Sublintype (TVar _) _ _):lc, fc) = do
  (lc', fc') <- break_composite bu (lc, fc)
  return (c:lc', fc')

break_composite bu (c@(Sublintype _ (TVar _) _):lc, fc) = do
  (lc', fc') <- break_composite bu (lc, fc)
  return (c:lc', fc')

-- Subtype constraints
break_composite bu ((Subtype (TBang n a) (TBang m b) info):lc, fc) = do
  break_composite bu ((Sublintype a b info):lc, (m,n):fc)


-- Everything else is a typing error
break_composite bu ((Subtype t u info):lc, fc) = do
  throwQ $ TypingError (pprint t) (pprint u)
  -- throw_TypingError t u info

