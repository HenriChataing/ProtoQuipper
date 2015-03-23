-- | ProtoQuipper uses a stack of reader monads in order to alleviate the complexity of a unique
-- state moned. The interpreter monad supports maintains the valuation map of the evaluated module,
-- and runs the operation on a circuit stack.

module Monad.Interpreter where

import Monad.Typer


-- | The typer state is able to generate fresh type and flag variables, and define the substitution
-- solution of the type constraints.
data InterpreterState = InterpreterState {

}

-- | The typer monad, runs in the core monad.
type Interpreter a = ReaderT TyperState Typer a


-- | Empty state.
empty :: InterpreterState
empty = InterpreterState {
  }
