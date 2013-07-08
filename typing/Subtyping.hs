module Subtyping (TypeConstraint(..), FlagConstraint(..), ConstraintSet(..),
                  is_trivial, is_atomic, is_composite, is_semi_composite,
                  is_one_sided,
                  constraint_unifier,
                  chain_constraints) where

import Classes
import Utils

import CoreSyntax

import Data.List as List

{-
  Definition of the generated constraints :
    - typing constraints, which can be either
        T <: U   or   A <: B
      where T, U are types ; and A, B linear types (no ! annotation)

    - flag constraints, of the form
        n <= m
      where n, m can be 0, 1 or a flag id

    - constraint sets, combining typing constraints and flag constraints
-}

data TypeConstraint =
    Linear LinType LinType
  | NonLinear Type Type

type FlagConstraint =
  (Flag, Flag)

type ConstraintSet =
  ([TypeConstraint], [FlagConstraint])

remove_details :: TypeConstraint -> TypeConstraint
--------------------------------------------------
remove_details (Linear t u) = Linear (undetailed t) (undetailed u)
remove_details c = c

{-
  Constraint properties
    - Atomicity : a constraint is atomic if of the form a <: b
      where a, b are type variables
  
    - Trivial : apply to constraints of the form T <: T or A <: A
      which are solved by reflexivity
 
    - Composite : apply to constraints of the form T <: U
      for any composite types T, U

    - Semi-composite : apply to constraints of the form a <: T or T <: a
      with a a type variable and T a composite type
-}

is_trivial :: TypeConstraint -> Bool
is_atomic :: TypeConstraint -> Bool
is_composite :: TypeConstraint -> Bool
is_semi_composite :: TypeConstraint -> Bool
-------------------------------------------
is_trivial (Linear a b) = a == b
is_trivial (NonLinear t u) = t == u

is_atomic (Linear t u) =
  case (undetailed t, undetailed u) of
    (TVar _, TVar _) -> True
    _ -> False
is_atomic _ = False

is_composite c = (not $ is_atomic c) && (not $ is_semi_composite c)

is_semi_composite (NonLinear _ _) = False
is_semi_composite (Linear t u) =
  case (undetailed t, undetailed u) of
    (TVar _, TVar _) -> False
    (TVar _, _) -> True
    (_, TVar _) -> True
    _ -> False

{-
  Check whether all the constraints of a list have the same property of being right / left sided, ie :
    - of the form a <: T : left-sided
    - of the from T <: a : right-sided

  The function is_right_sided returns true if all the constraints are right sided
               is_left_sided returns true if all the constraints are left sided
               is_one_sided returns true if either is_left_sided or is_right_sided is true
-}

is_one_sided :: [TypeConstraint] -> Bool
is_left_sided :: [TypeConstraint] -> Bool
is_right_sided :: [TypeConstraint] -> Bool
---------------------------------------
is_one_sided [] = True
is_one_sided ((Linear t u):cset) =
  case (undetailed t, undetailed u) of
    (TVar _, _) -> is_left_sided cset
    (_, TVar _) -> is_right_sided cset
    _ -> False
is_one_sided _ = False

is_left_sided [] = True
is_left_sided ((Linear t u):cset) =
  case (undetailed t, undetailed u) of
    (TVar _, _) -> is_left_sided cset
    _ -> False
is_left_sided _ = False

is_right_sided [] = True
is_right_sided ((Linear t u):cset) =
  case (undetailed t, undetailed u) of
    (_, TVar _) -> is_right_sided cset
    _ -> False
is_right_sided _ = False

{-
  Finds the 'most general unifier' (not in the sense of unification) of a list of type constraints.
  The unifier is a type chosen to carry the most information about the structure of the types of the constraints
  (which has to be the same for each type). For example, the chosen unifier of ((a -> b) -> c) and (d -> (e -> f)) is
  ((a -> b) -> (e -> f))

  The list given as argument is assumed to form a 'class' of semi-composite constraints :
    - all the constraints must be semi-composite
    - all the variable of the semi-composite constraints are of the same age class (ie linked together by atomic constraints)
-}
constraint_unifier :: [TypeConstraint] -> LinType
-------------------------------------------------
constraint_unifier constraints =
  let comptypes = List.map (\c -> case remove_details c of
                                    Linear (TVar _) t -> t
                                    Linear t (TVar _) -> t) constraints
  in
  list_unifier comptypes

{-
  Attempts to link together the input constraints, for example the set { b <: U, a <: b, T <: a } can
  be rearranged as { T <: a <: b <: U }

  The result is used in the unfication algorithm : if the constraints can be linked, the approximation
    { T <: a <: b <: U }  <=>  a :=: b :=: T, { T <: U } can be made
  (Since if a solution of the approximation can be found, it is also a solution of the initial set, and conversely)
-}
chain_constraints :: [TypeConstraint] -> (Bool, [TypeConstraint])
chain_left_to_right :: [TypeConstraint] -> Int -> [TypeConstraint] -> (Bool, [TypeConstraint])
chain_right_to_left :: [TypeConstraint] -> Int -> [TypeConstraint] -> (Bool, [TypeConstraint])
----------------------------------------------------------------------------------------------
chain_left_to_right chain endvar [] = (True, List.reverse chain)
chain_left_to_right chain endvar l =
  case List.find (\c -> case remove_details c of
                          Linear (TVar y) _ -> y == endvar
                          _ -> False) l of
    Just c -> case remove_details c of
                Linear (TVar _) (TVar y) -> chain_left_to_right (c:chain) y (List.delete c l)
                _ -> if List.length l == 1 then
                       (True, List.reverse (c:chain))
                     else
                       (False, [])
    Nothing -> (False, [])

chain_right_to_left chain endvar [] = (True, chain)
chain_right_to_left chain endvar l =
  case List.find (\c -> case remove_details c of
                          Linear _ (TVar y) -> y == endvar
                          _ -> False) l of
    Just c -> case remove_details c of
                Linear (TVar y) (TVar _) -> chain_right_to_left (c:chain) y (List.delete c l)
                _ -> if List.length l == 1 then
                       (True, c:chain)
                     else
                       (False, [])
    Nothing -> (False, [])

chain_constraints l =
  case List.find (\c -> case remove_details c of
                          Linear (TVar _) _ -> False
                          _ -> True) l of
    Just c -> case remove_details c of
                Linear _ (TVar y) -> chain_left_to_right [c] y (List.delete c l)
                _ -> error "Unreduced composite constraint"
  
    Nothing -> case List.find (\c -> case remove_details c of
                                       Linear _ (TVar _) -> False
                                       _ -> True) l of
                 Just c -> case remove_details c of
                             Linear (TVar y) _ -> chain_right_to_left [c] y (List.delete c l)
                             _ -> error "Unreduced composite constraint"
                 Nothing -> error "Only atomic constraints"

{-
  Instance declaration

  TypeConstraint is instance of
    - PPrint
    - Param
    - Eq

  FlagConstraint is instance of
    - PPrint

  ConstraintSet is instance of
    - PPrint
-}

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

instance Eq TypeConstraint where
  (==) (Linear t u) (Linear t' u') = t == t' && u == u'
  (==) (NonLinear t u) (NonLinear t' u') = t == t' && u == u'
  (==) _ _ = False

instance PPrint FlagConstraint where
  pprint (m, n) =
    (if m < 2 then
       show m
     else
       subvar 'f' m) ++ " <= " ++
    (if n < 2 then
       show n
     else
       subvar 'f' n)

  sprintn _ c = pprint c
  sprint c = pprint c

instance PPrint ConstraintSet where
  pprint (lcs, fcs) =
    let screenw = 120 in
    let plcs = List.map pprint lcs in
    let maxw = List.maximum $ List.map List.length plcs in
    let nline = screenw `quot` (maxw + 5) in 

    let slcons = fst $ List.foldl (\(s, nth) pc ->
                        let padding = List.take (maxw - List.length pc + 5) $ List.repeat ' ' in

                        if nth == 0 then
                          (s ++ "\n" ++ pc ++ padding, nline)
                        else
                          (s ++ pc ++ padding, nth-1)) ("", nline+1) plcs
    in

    let pfcs = List.map pprint fcs in
    let maxw = List.maximum $ List.map List.length pfcs in
    let nline = screenw `quot` (maxw + 5) in

    let sfcons = fst $ List.foldl (\(s, nth) pc ->
                        let padding = List.take (maxw - List.length pc + 5) $ List.repeat ' ' in

                        if nth == 0 then
                          (s ++ "\n" ++ pc ++ padding, nline)
                        else
                          (s ++ pc ++ padding, nth-1)) ("", nline+1) pfcs
    in

    slcons ++ "\n" ++ sfcons

  sprintn _ cs = pprint cs
  sprint cs = pprint cs
