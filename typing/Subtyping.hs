module Subtyping where

import Classes

import CoreSyntax

import Data.List as List

-------------------------
-- Various constraints --

data TypeConstraint =
    Linear LinType LinType
  | NonLinear Type Type

type FlagConstraint =
  (Flag, Flag)      -- n <= m

type ConstraintSet =
  ([TypeConstraint], [FlagConstraint])


instance Eq TypeConstraint where
  (==) (Linear t u) (Linear t' u') = t == t' && u == u'
  (==) (NonLinear t u) (NonLinear t' u') = t == t' && u == u'
  (==) _ _ = False

-- Constraint properties
trivial :: TypeConstraint -> Bool
atomic :: TypeConstraint -> Bool
-----------------------------------
trivial (Linear (TVar x) (TVar y)) = x == y
trivial _ = False

atomic (Linear (TVar _) (TVar _)) = True
atomic _ = False

-- Check whether the semi-composite constraints are all one-sided or not
one_sided :: [TypeConstraint] -> Bool
left_sided :: [TypeConstraint] -> Bool
right_sided :: [TypeConstraint] -> Bool
-----------------------------------------------
one_sided [] = True
one_sided ((Linear (TVar _) _):cset) = left_sided cset
one_sided ((Linear _ (TVar _)):cset) = right_sided cset

left_sided [] = True
left_sided ((Linear (TVar _) _):cset) = left_sided cset
left_sided _ = False

right_sided [] = True
right_sided ((Linear _ (TVar _)):cset) = right_sided cset
right_sided _ = False

-- Looking for the most general type
linear_type_unifier :: LinType -> LinType -> LinType  -- Find an unifier of two linear types
type_unifier :: Type -> Type -> Type
list_unifier :: [LinType] -> LinType        -- Same as type_unifier, but applied to a whole list of types
constraint_unifier :: [TypeConstraint] -> LinType  -- Take in semi-composite constraints a <: T or T <: a, and get an unifier of the composite types
------------------------------------------------
linear_type_unifier TUnit _ = TUnit
linear_type_unifier _ TUnit = TUnit
linear_type_unifier TBool _ = TBool
linear_type_unifier _ TBool = TBool
linear_type_unifier TQBit _ = TQBit
linear_type_unifier _ TQBit = TQBit
linear_type_unifier (TVar _) t = t
linear_type_unifier t (TVar _) = t
linear_type_unifier (TArrow t u) (TArrow t' u') = TArrow (type_unifier t t') (type_unifier u u')
linear_type_unifier (TTensor t u) (TTensor t' u') = TTensor (type_unifier t t') (type_unifier u u')
linear_type_unifier (TCirc t u) (TCirc t' u') = TCirc (type_unifier t t') (type_unifier u u')
type_unifier (TExp m t) (TExp _ u) = TExp m $ linear_type_unifier t u

list_unifier (t:ct) =
  List.foldl (\unif u -> linear_type_unifier unif u) t ct

constraint_unifier constraints =
  let comptypes = List.map (\c -> case c of
                                    Linear (TVar _) t -> t
                                    Linear t (TVar _) -> t) constraints
  in
  list_unifier comptypes

-- Chaining constraints together
chain_constraints :: [TypeConstraint] -> (Bool, [TypeConstraint])
chain_left_to_right :: [TypeConstraint] -> Int -> [TypeConstraint] -> (Bool, [TypeConstraint])
----------------------------------------------------------------------------------------------------
chain_left_to_right chain endvar [] = (True, List.reverse chain)
chain_left_to_right chain endvar l =
  case List.find (\c -> case c of
                          Linear (TVar y) _ -> y == endvar
                          _ -> False) l of
    Just c -> case c of
                Linear (TVar _) (TVar y) -> chain_left_to_right (c:chain) y (List.delete c l)
                _ -> if List.length l == 1 then
                       (True, List.reverse (c:chain))
                     else
                       (False, [])
    Nothing -> (False, [])

chain_right_to_left chain endvar [] = (True, chain)
chain_right_to_left chain endvar l =
  case List.find (\c -> case c of
                          Linear _ (TVar y) -> y == endvar
                          _ -> False) l of
    Just c -> case c of
                Linear (TVar y) (TVar _) -> chain_right_to_left (c:chain) y (List.delete c l)
                _ -> if List.length l == 1 then
                       (True, c:chain)
                     else
                       (False, [])
    Nothing -> (False, [])

chain_constraints l =
  case List.find (\c -> case c of
                          Linear (TVar _) _ -> False
                          _ -> True) l of
    Just c -> case c of
                Linear _ (TVar y) -> chain_left_to_right [c] y (List.delete c l)
                _ -> error "Unreduced composite constraint"
  
    Nothing -> case List.find (\c -> case c of
                                       Linear _ (TVar _) -> False
                                       _ -> True) l of
                 Just c -> case c of
                             Linear (TVar y) _ -> chain_right_to_left [c] y (List.delete c l)
                             _ -> error "Unreduced composite constraint"
                 Nothing -> error "Only atomic constraints"


instance Param TypeConstraint where
  free_var (Linear t u) = free_var t ++ free_var u
  free_var (NonLinear t u) = free_var t ++ free_var u  

  subs_var a b (Linear t u) = Linear (subs_var a b t) (subs_var a b u)
  subs_var a b (NonLinear t u) = NonLinear (subs_var a b t) (subs_var a b u)

instance PPrint TypeConstraint where
  pprint (Linear t u) = pprint t ++ " <: " ++ pprint u
  pprint (NonLinear t u) = pprint t ++ " <: " ++ pprint u
  sprintn _ c = pprint c
  sprint c = pprint c
