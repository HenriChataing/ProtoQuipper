{-# LANGUAGE MultiParamTypeClasses #-}

-- | Defines the simplified syntax produced by the preliminary simplifications perfomed by the
-- compiler.
module Compiler.Syntax where

import Utils
import Classes

import Monad.Error

import Data.IntMap as IntMap
import Data.IntSet as IntSet


-- | The definition of values.
data Value =
    VVar Variable              -- ^ A local variable _ function or not.
  | VInt Int                   -- ^ An integer.
  | VLabel Variable            -- ^ The label of an extern function.
  | VGlobal Variable           -- ^ A reference to a global variable.
  deriving (Show, Eq)

-- | Destruct a 'VVar' value.
unVVar :: Value -> Variable
unVVar (VVar x) = x
unVVar _ = throwNE $ ProgramError "CExpr:unVVar: illegal argument"


-- | Are considered free variables only variables bound in a local scope.
instance TermObject Value where
  freevar (VVar x) = IntSet.singleton x
  freevar _ = IntSet.empty


instance Subs Value Value where
  subs x v (VVar y) = if x == y then v else VVar y
  subs _ _ v = v


-- | Context of values used during the translation.
type CContext = IntMap Value


-- | Retrieve a value from the context.
value :: CContext -> Variable -> Value
value vals x =
  case IntMap.lookup x vals of
    Just v -> v
    Nothing -> VVar x


-- | Definition of expressions.
data CExpr =
    CFun Variable [Variable] CExpr CExpr           -- ^ Function abstraction: @fun x1 .. xN -> t@. All definitions are recursive.
  | CTailApp Value [Value]                         -- ^ Application of a function in tail position: @t u@.
  | CApp Value [Value] Variable CExpr              -- ^ Application of a function, with a continuation.
  | CTuple [Value] Variable CExpr                  -- ^ Construction of a tuple: @(/t/1, .. , /t//n/)@.
  | CAccess Int Value Variable CExpr               -- ^ Access the nth element of a tuple.
  | CSwitch Value [(Int, CExpr)] CExpr             -- ^ Switch condition (with a default target).
  | CRet Value                                     -- ^ Return a value. This instruction is terminal.
  | CSet Variable Value                            -- ^ This instruction is terminal, and specific to global variables, where it is necessary to set a specific variable.
  | CFree Value CExpr                              -- ^ Assuming the value represents a tuple, free the memory and continue with the expression.
  | CError String                                  -- ^ This instruction is terminal, and throws an error message.
  deriving Show
