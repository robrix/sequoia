-- | Lowering (running) “pure” monads to a value.
module Sequoia.Monad.Run
( -- * Lowering
  MonadRun(..)
) where

import Data.Function
import Data.Functor.Identity

-- Lowering

class Monad m => MonadRun m where
  withRun :: ((m r -> r) -> m a) -> m a

instance MonadRun ((->) a) where
  withRun b = b =<< (&)

instance MonadRun Identity where
  withRun b = b runIdentity
