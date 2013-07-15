-- | This module defines all that is needed to work with sub-typing and flag constraints

module Subtyping (
  -- Constraints definition
  TypeConstraint(..),
  FlagConstraint(..),
  ConstraintSet(..),
  -- Operation on constraints
  (<:),
  (<>),
  is_trivial, is_atomic, is_composite, is_semi_composite,
  is_one_sided,
  constraint_unifier,
  chain_constraints) where


import Classes
import Utils

import CoreSyntax
import CorePrinter

import Data.List as List



