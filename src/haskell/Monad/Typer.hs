-- | ProtoQuipper uses a stack of reader monads in order to alleviate the complexity of a unique
-- state moned. The typer monad supports the generation of type and flag variables, and contains
-- the type substitution solution of the type constraints.

module Monad.Typer where

import Utils
import Parsing.Location

import Language.Constructor

import Core.Syntax (Type)

import Monad.Core as Core
import Monad.Error

import Control.Monad.Trans
import Control.Monad.Trans.State


-- | The typer state is able to generate fresh type and flag variables, and define the substitution
-- solution of the type constraints.
data TyperState = TyperState {

}

-- | The typer monad, runs in the core monad.
type Typer = StateT TyperState Core


-- | Empty state.
empty :: TyperState
empty = TyperState {
  }


---------------------------------------------------------------------------------------------------
-- * Type map.

-- | Replace all mapped type variables in the given type.
-- TODO: implement.
solveType :: Type -> Typer Type
solveType typ = return typ


---------------------------------------------------------------------------------------------------
-- * Lifting.

log :: Int -> String -> Typer ()
log lvl msg = lift $ Core.log lvl msg

warning :: Warning -> Maybe Extent -> Typer ()
warning warn ext = lift $ Core.warning warn ext

runCore :: Core a -> Typer a
runCore computation = lift $ computation
