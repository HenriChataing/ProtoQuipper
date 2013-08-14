-- | This module provides functions that operate constraint sets: reduction mostly.
module Typing.Subtyping where

import Classes

import Typing.CoreSyntax
import Typing.CorePrinter

import Monad.QuipperError
import Monad.QpState

import qualified Data.List as List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap

-- | Identifies the trivial flag constraints.
non_trivial :: RefFlag -> RefFlag -> Bool
non_trivial m n =
  (m /= n && n /= 1 && m /= 0)



-- | Using the type specifications registered in the state monad, unfolds any subtyping
-- constraints of the form  user a <: user a'. This functions assumes that the two type
-- names are the same, and that the right number of arguments has been given.
unfold_user_constraint :: String -> [Type] -> String -> [Type] -> QpState ConstraintSet
unfold_user_constraint utyp arg utyp' arg' = do
  -- Retrieve the specification of the type
  spec <- type_spec utyp
  -- The constraints
  (a, a', cset) <- return $ subtype spec

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



-- | Applies the function unfold_user_constraints to the constraints in a constraint set.
unfold_user_constraints_in_set :: ConstraintSet -> QpState ConstraintSet
unfold_user_constraints_in_set ([], fc) = return ([], fc)
unfold_user_constraints_in_set ((Sublintype (TUser utyp args) (TUser utyp' args') _):lc, fc) = do
  cset <- unfold_user_constraint utyp args utyp' args'
  cset' <- unfold_user_constraints_in_set (lc, fc)
  return $ cset <> cset'
unfold_user_constraints_in_set (c:lc, fc) = do
  (lc', fc') <- unfold_user_constraints_in_set (lc, fc)
  return (c:lc', fc')



-- | Reduces the composite constrainst of a constraint set, leaving only atomic
-- and semi composite constraints. The boolean argument indicates whether to break user
-- type constraints or not. When this flag is set, the user type constraints are left untouched:
-- this is useful for the extension of the subtyping relations to algebraic types, where one wants
-- to reduce only the non-algebraic type constraints.
break_composite :: Bool -> ConstraintSet -> QpState ConstraintSet

-- Nothing to do
break_composite bu ([], lc) = return ([], lc)

-- Subtype constraints
break_composite bu ((Subtype (TBang n t) (TBang m TQbit) info):lc, fc) = do
  unset_flag n
  unset_flag m
  break_composite bu ((Sublintype t TQbit info):lc, fc)

break_composite bu ((Subtype (TBang n TQbit) (TBang m t) info):lc, fc) = do
  unset_flag n
  unset_flag m
  break_composite bu ((Sublintype TQbit t info):lc, fc)

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


-- Qbit against QBit : removed
break_composite bu ((Sublintype TQbit TQbit _):lc, fc) = do
  break_composite bu (lc, fc)


-- Arrow against arrow
  -- T -> U <: T' -> U' 
-- Into
  -- T' <: T && U <: U'
break_composite bu ((Sublintype (TArrow t u) (TArrow t' u') info):lc, fc) = do
  intype <- case in_type info of
              Just a -> return $ Just a
              Nothing -> return $ Just $ if actual info then TArrow t u else TArrow t' u'

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
                Nothing -> return $ Just $ if actual info then TTensor tlist else TTensor tlist'

    comp <- return $ List.map (\(t, u) -> Subtype t u info { in_type = intype }) $ List.zip tlist tlist'
    break_composite bu (comp ++ lc, fc)

  else do
    throw_TypingError (TTensor tlist) (TTensor tlist') info


-- User type against user type
-- The result of breaking this kind of constraints has been placed in the specification of the user type
-- It need only be instanciated with the current type arguments
break_composite bu ((Sublintype (TUser utyp arg) (TUser utyp' arg') info):lc, fc) = do
  if utyp == utyp' then do
    
    if bu then do
      intype <- case in_type info of
                  Just a -> return $ Just a
                  Nothing -> return $ Just $ if actual info then TUser utyp arg else TUser utyp' arg'

      cset <- unfold_user_constraint utyp arg utyp' arg'

      -- This one may be reversed : will have to check
      break_composite bu $ (cset & info { in_type = intype }) <> (lc, fc)

    else do
      cset <- break_composite bu (lc, fc)
      return $ [Sublintype (TUser utyp arg) (TUser utyp' arg') info] <> cset
      
  else
    throw_TypingError (TUser utyp arg) (TUser utyp' arg') info


-- Circ against Circ
  -- circ (T, U) <: circ (T', U')
-- Into
  -- T' <: T && U <: U'
-- The flags don't really matter, as they can take any value, so no constraint m <= n is generated
break_composite bu ((Sublintype (TCirc t u) (TCirc t' u') info):lc, fc) = do
  intype <- case in_type info of
              Just a -> return $ Just a
              Nothing -> return $ Just $ if actual info then TCirc t u else TCirc t' u'

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
  if non_trivial n m then
    break_composite bu ((Sublintype a b info):lc, (m,n):fc)
  else
    break_composite bu ((Sublintype a b info):lc, fc)


-- Everything else is a typing error
break_composite bu ((Sublintype t u info):lc, fc) = do
  throw_TypingError t u info




-- | Equivalence classes.
data Equiv a = Eqv {
  cmap :: IntMap Int,
  classes :: IntMap ([Variable], [a])
}


new_with_class :: [Variable] -> Equiv a
new_with_class c@(a:_) =
  Eqv { cmap = IMap.fromList $ List.map (\b -> (b, a)) c,
        classes = IMap.singleton a (c, []) }


in_class :: Variable -> Equiv a -> (Int, Equiv a)
in_class x eqv =
  case IMap.lookup x $ cmap eqv of
    Just c -> (c, eqv)
    Nothing -> (x, eqv { cmap = IMap.insert x x $ cmap eqv,
                         classes = IMap.insert x ([x],[]) $ classes eqv })


class_contents :: Int -> Equiv a -> ([Variable], [a])
class_contents c eqv =
  case IMap.lookup c $ classes eqv of
    Just cts -> cts
    Nothing -> ([], [])


merge_classes :: Int -> Int -> a -> Equiv a -> Equiv a
merge_classes c c' a eqv =
  if c /= c' then
    let (cts, as) = class_contents c eqv
        (cts', as') = class_contents c' eqv in 
    eqv { cmap = IMap.map (\d -> if d == c' then c else d) $ cmap eqv,
          classes = IMap.update (\_ -> Just (cts ++ cts', a:(as ++ as'))) c $ IMap.delete c' $ classes eqv }
  else
    eqv { classes = IMap.update (\(cts, as) -> Just (cts, a:as)) c $ classes eqv }


insert_constraint :: Variable -> Variable -> a -> Equiv a -> Equiv a
insert_constraint x y c eqv =
  let (cx, eqv') = in_class x eqv
      (cy, eqv'') = in_class y eqv' in
  merge_classes cx cy c eqv''


-- | Removes unaccessbiel flag and type constraints from a constraint set, based on the variables
-- appearing in the type.
clean_constraint_set :: Type -> ConstraintSet -> ([Variable], [RefFlag], ConstraintSet)
clean_constraint_set a (lc, fc) =
  let ff = free_flag a
      fv = free_typ_var a in

  -- Clean the type constraints
  let (ctsv, lc') = case fv of
                     [] -> ([], [])
                     (x:_) -> let eqvl = new_with_class fv in
                              let eqvl' = List.foldl (\eqv c@(Sublintype (TVar x) (TVar y) _) ->
                                                        insert_constraint x y c eqv) eqvl lc in
                              let (cl, _) = in_class x eqvl' in
                              class_contents cl eqvl' in

  -- Clean the flag constraints
  let (ctsf, fc') = case ff of
                     [] -> ([], [])
                     (x:_) -> let eqvf = new_with_class ff in
                              let eqvf' = List.foldl (\eqv c@(n, m) ->
                                                        insert_constraint n m c eqv) eqvf fc in
                              let (cf, _) = in_class x eqvf' in
                              class_contents cf eqvf' in

  (ctsv, ctsf, (lc', fc'))


