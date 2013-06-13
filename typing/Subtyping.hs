module Subtyping where

import Classes

import CoreSyntax


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

instance Param LinearConstraint where
  free_var (t, u) = free_var t ++ free_var u
  
  subs_var a b (t, u) = (subs_var a b t, subs_var a b u)

  subs _ _ c = c

instance PPrint LinearConstraint where
  pprint (t, u) = pprint t ++ " <: " ++ pprint u
  sprintn _ c = pprint c
  sprint c = pprint c
