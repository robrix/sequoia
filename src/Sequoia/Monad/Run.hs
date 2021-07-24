-- | Lowering (running) “pure” monads to a value.
module Sequoia.Monad.Run
( -- * Lowering
  MonadRun(..)
) where

-- Lowering

class Monad m => MonadRun m where
  withRun :: ((m r -> r) -> m a) -> m a
