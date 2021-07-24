-- | Lowering (running) “pure” monads to a value.
module Sequoia.Monad.Run
( -- * Lowering
  MonadRun(..)
) where

import Data.Function

-- Lowering

class Monad m => MonadRun m where
  withRun :: ((m r -> r) -> m a) -> m a

instance MonadRun ((->) a) where
  withRun b = b =<< (&)
