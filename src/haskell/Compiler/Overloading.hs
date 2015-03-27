-- | Unbox operators need to be overloaded to work with all types. This module updates the code and
-- types to adapt to this constraint.

module Compiler.Overloading where

import Classes
import Utils

import Parsing.Location (extent_unknown)

import Language.Constructor

import Monad.Compiler
import Monad.Error

import Core.Syntax as Core
import Compiler.Circuits

import Control.Monad.Trans
import Control.Monad.Trans.State
import Data.List as List
import Data.IntMap as IntMap


-- | Context of unbox variables.
type Overloading = StateT [(Type, Variable)] Compiler


-- | Return either the original unbox operator, if the type is concrete, or one of the argument given
-- in the list that has the appropriate type.
whichUnbox :: Type -> Info -> Overloading Expr
whichUnbox ctyp info =
  if (isConcrete ctyp) then return $ EUnbox info
  else do
    context <- get
    case List.find (equalsLinear ctyp . fst) context of
      Just (_, x) -> return $ EVar info x
      Nothing -> do
        -- The unbox type is not available, generate a new variable with the required type, and push
        -- it to the context.
        x <- lift $ createVariable "u"
        modify ((ctyp, x):)
        return $ EVar info x


-- | Modify an expression to disambiguate the use of the unbox operator: when the type can be inferred
-- automically (in a non polymorphic context), then the operator is untouched, else, the function
-- using the unbox is modified to take the unbox operator as argument.
disambiguate :: IntMap (Type, [Type]) -> Expr -> Overloading Expr

-- The unbox reference, if of no decided type, is replaced by a variable (reference to an unbox operator
-- with same type).
disambiguate _ (EUnbox info) = do
  ctyp <- lift $ solveType $ Core.typ info
  whichUnbox ctyp info

-- For each variable, we must check whether its type has been modified to disambiguate an unbox operators.
-- If this is the case, the unbox arguments must be provided for.
disambiguate modified (EVar info x) =
  case IntMap.lookup x modified of
    Nothing -> return $ EVar info x
    Just (typ, args) -> do
      -- If the type of the variable is concrete (no leftover type variables), then the unbox operators
      -- to apply can easily be derived.
      typ' <- lift $ solveType $ Core.typ info
      let b = bindTypes typ typ'
      let args' = List.map (mapType b) args
      -- Use the function whichUnbox to find the arguments, and build the application of the variable
      -- to the additional unbox arguments.
      List.foldl (\rec arg -> do
          e <- rec
          x <- whichUnbox arg $ info { Core.typ = arg }
          return $ EApp e x
        ) (return $ EVar info x) args'

-- Only recursive calls for the next constructors.
disambiguate modified (EFun info arg body) = do
  body' <- disambiguate modified body
  return $ EFun info arg body'

disambiguate modified (EApp e f) = do
  e' <- disambiguate modified e
  f' <- disambiguate modified f
  return $ EApp e' f'

disambiguate modified (EIf e f g) = do
  e' <- disambiguate modified e
  f' <- disambiguate modified f
  g' <- disambiguate modified g
  return $ EIf e' f' g'

disambiguate modified (EDatacon info cons (Just e)) = do
  e' <- disambiguate modified e
  return $ EDatacon info cons $ Just e'

disambiguate modified (EMatch test cases) = do
  test' <- disambiguate modified test
  cases' <- List.foldr (\(Binding p e) rec -> do
      cases <- rec
      e' <- disambiguate modified e
      return $ (Binding p e'):cases) (return []) cases
  return $ EMatch test' cases'

disambiguate modified (ETuple info tuple) = do
  tuple' <- List.foldr (\e rec -> do
      tuple <- rec
      e' <- disambiguate modified e
      return $ e':tuple) (return []) tuple
  return $ ETuple info tuple'

disambiguate modified (ECoerce e _) =
  disambiguate modified e

--disambiguate arg mod (C.EGlobal ref v) = do
--  cc <- call_convention v
--  case cc of
--    Nothing -> do
--        return (C.EGlobal ref v)

--    Just args -> do
--        t <- global_type v
--        let typ = C.typeOfScheme t
--        -- If the type of the variable is concrete (no leftover type variables), then
--        -- the unbox operators to apply can easily be derived.
--        ri <- ref_info_err ref
--        typ' <- map_type $ C.rtype ri
--        b <- C.bindTypes typ typ'
--        let args' = List.map (subs b) args
--        -- Use the function whichUnbox to decide the arguments
--        args' <- List.foldr (\a rec -> do
--              as <- rec
--              wua <- whichUnbox a arg
--              case wua of
--                Left _ -> do
--                    -- The type is concrete, create a reference to store it
--                    ref <- create_ref
--                    update_ref ref (\ri -> Just ri { C.rtype = a })
--                    return $ (C.EUnbox ref):as

--                Right v ->
--                    -- The type os not concrete, but a variable holding the right unbox implementation has been found
--                    return $ (C.EVar 0 v):as) (return []) args'
--        -- Finish by giving the unbox operators as arguments of the variable.
--        List.foldl (\rec a -> do
--              e <- rec
--              return $ C.EApp e a) (return $ C.EGlobal ref v) args'


disambiguate modified (ELet r binder value body) = do
  context <- get -- Extract the context before evaluating the value (for future reference).
  value' <- disambiguate modified value -- Disambiguate the calls from the value.
  -- Retrieve the context after the evaluation of the value, and check which new unboxes were required.
  context' <- get
  let require = List.deleteFirstsBy (\(_, x) (_, x') -> x == x') context' context
  -- Reset the context to its previous state.
  put context
  -- Test whether the list is empty or not.
  case require of
    -- Nothing more to do, continue with the body.
    [] -> do
      body' <- disambiguate modified body
      return $ ELet r binder value' body'

    -- Add new arguments to the variable x matching the missing unbox types.
    _ -> do
      case (binder, value') of
        (PWildcard info, _) -> do
          body' <- disambiguate modified value -- New arguments ignored.
          -- Assemble the final expression.
          let value'' = List.foldl (\value (_, x) -> EFun info (PVar info x) value) value' require
          return $ ELet r binder value'' body'

        (PVar info x, _) -> do
          -- Retrieve the (polymorphic) type of the variable
          qtyp <- lift $ solveType $ Core.typ info

          -- Check whether the variable is global or not
          --g <- is_global x
          --if g then set_call_convention x need -- Specify the calling convention for x
          --else return () -- Do nothing

          -- Update the modifie environment.
          let modified' = IntMap.insert x (qtyp, List.map fst require) modified
          -- Convert the body in the new modified environment (without the new arguments).
          body' <- disambiguate modified' body
          -- Assemble the final expression
          let value'' = List.foldl (\value (_, x) -> EFun info (PVar info x) value) value' require
          return $ ELet r binder value'' body'

        -- Tuples can generally not be transformed, except in this case where we can explode the tuple.
        (PTuple _ plist, ETuple _ elist) -> do
          let elet = List.foldl (\body (binder, value) -> ELet r binder value body) body (List.zip plist elist)
          disambiguate modified elet

        -- Same thing for data constructors.
        (PDatacon _ dcon (Just binder), EDatacon info dcon' (Just value)) | dcon == dcon' -> do
            disambiguate modified $ ELet r binder value body
                                                                          | otherwise -> do
            -- This case always leads to a matching error. Raise a warning
            lift $ warning FailedMatch $ Just $ Core.extent info
            return $ EError (show (Core.extent info) ++ ":pattern error")

        -- All other cases should be unreachable
        (p, _) -> fail $ "Overloading:disambiguate: unexpected pattern: " ++ pprint p

disambiguate _ e = return e


-- |  Modify an expression to disambiguate the use of the unbox operator: when the type can be inferred
-- automically (in a non polymorphic context), then the operator is untouched, else, the function
-- using the unbox is modified to take the unbox operator as argument.
disambiguateUnboxCalls :: Expr -> Compiler Expr
disambiguateUnboxCalls code = do
  (code', context) <- runStateT (disambiguate IntMap.empty code) [] -- Run the disambiguation in a initially empty context.
  if (context /= []) then -- Some unbox operators could not be resolved, abort.
    fail $ "Overloading:disambiguate: unable to resolve all unbox operators"
  else return code
