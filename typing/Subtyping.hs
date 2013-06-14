module Subtyping where

import Classes

import CoreSyntax

import Data.List as List

-------------------------
-- Various constraints --

type LinearConstraint =         
  (Type, Type)      -- T <: U

type FlagConstraint =
  (Flag, Flag)      -- n <= m

type ConstraintSet =
  ([LinearConstraint], [FlagConstraint])


-- Constraint properties
trivial :: LinearConstraint -> Bool
atomic :: LinearConstraint -> Bool
-----------------------------------
trivial (TVar x, TVar y) = x == y
trivial _ = False

atomic (TVar _, TVar _) = True
atomic _ = False

-- Check whether the semi-composite constraints are all one-sided or not
one_sided :: [LinearConstraint] -> Bool
left_sided :: [LinearConstraint] -> Bool
right_sided :: [LinearConstraint] -> Bool
-----------------------------------------------
one_sided [] = True
one_sided ((TVar _, _):cset) = left_sided cset
one_sided ((_, TVar _):cset) = right_sided cset

left_sided [] = True
left_sided ((TVar _, _):cset) = left_sided cset
left_sided _ = False

right_sided [] = True
right_sided ((_, TVar _):cset) = right_sided cset
right_sided _ = False

-- Looking for the most general type
type_unifier :: Type -> Type -> Type  -- Find an unifier of two types
list_unifier :: [Type] -> Type        -- Same as type_unifier, but applied to a whole list of types
constraint_unifier :: [LinearConstraint] -> Type  -- Take in semi-composite constraints a <: T or T <: a, and get an unifier of the composite types
------------------------------------------------
type_unifier TUnit _ = TUnit
type_unifier _ TUnit = TUnit
type_unifier (TVar _) t = t
type_unifier t (TVar _) = t
type_unifier (TArrow t u) (TArrow t' u') = TArrow (type_unifier t t') (type_unifier u u')
type_unifier (TTensor t u) (TTensor t' u') = TTensor (type_unifier t t') (type_unifier u u')
type_unifier (TExp _ t) (TExp _ u) = type_unifier t u
type_unifier (TExp _ t) u = type_unifier t u
type_unifier t (TExp _ u) = type_unifier t u

list_unifier (t:ct) =
  List.foldl (\unif u -> type_unifier unif u) t ct

constraint_unifier constraints =
  let comptypes = List.map (\c -> case c of
                                    (TVar _, t) -> t
                                    (t, TVar _) -> t) constraints
  in
  list_unifier comptypes

-- Chaining constraints together
chain_constraints :: [LinearConstraint] -> (Bool, [LinearConstraint])
chain_left_to_right :: [LinearConstraint] -> Int -> [LinearConstraint] -> (Bool, [LinearConstraint])
----------------------------------------------------------------------------------------------------
chain_left_to_right chain endvar [] = (True, List.reverse chain)
chain_left_to_right chain endvar l =
  case List.find (\c -> case c of
                          (TVar y, _) -> y == endvar
                          _ -> False) l of
    Just c -> case c of
                (TVar _, TVar y) -> chain_left_to_right (c:chain) y (List.delete c l)
                _ -> if List.length l == 1 then
                       (True, List.reverse (c:chain))
                     else
                       (False, [])
    Nothing -> (False, [])

chain_right_to_left chain endvar [] = (True, chain)
chain_right_to_left chain endvar l =
  case List.find (\c -> case c of
                          (_, TVar y) -> y == endvar
                          _ -> False) l of
    Just c -> case c of
                (TVar y, TVar _) -> chain_right_to_left (c:chain) y (List.delete c l)
                _ -> if List.length l == 1 then
                       (True, c:chain)
                     else
                       (False, [])
    Nothing -> (False, [])

chain_constraints l =
  case List.find (\c -> case c of
                          (TVar _, _) -> False
                          _ -> True) l of
    Just c -> case c of
                (_, TVar y) -> chain_left_to_right [c] y (List.delete c l)
                _ -> error "Unreduced composite constraint"
  
    Nothing -> case List.find (\c -> case c of
                                       (_, TVar _) -> False
                                       _ -> True) l of
                 Just c -> case c of
                             (TVar y, _) -> chain_right_to_left [c] y (List.delete c l)
                             _ -> error "Unreduced composite constraint"
                 Nothing -> error "Only atomic constraints"


instance Param LinearConstraint where
  free_var (t, u) = free_var t ++ free_var u
  
  subs_var a b (t, u) = (subs_var a b t, subs_var a b u)

  subs _ _ c = c

instance PPrint LinearConstraint where
  pprint (t, u) = pprint t ++ " <: " ++ pprint u
  sprintn _ c = pprint c
  sprint c = pprint c
