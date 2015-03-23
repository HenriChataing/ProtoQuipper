-- | ProtoQuipper uses a stack of reader monads in order to alleviate the complexity of a unique
-- state moned. The typer monad supports the generation of type and flag variables, and contains
-- the type substitution solution of the type constraints.

module Monad.Typer where

import Monad.Core


-- | The typer state is able to generate fresh type and flag variables, and define the substitution
-- solution of the type constraints.
data TyperState = TyperState {

}

-- | The typer monad, runs in the core monad.
type Typer a = ReaderT TyperState Core a


-- | Empty state.
empty :: TyperState
empty = TyperState {
  }
