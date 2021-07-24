-- | Lowering (running) “pure” monads to a value.
module Sequoia.Monad.Run
( -- * Lowering
  MonadRun(..)
  -- * Construction
, fn
  -- * Defaults
, distributeRun
) where

import Data.Functor.Identity

-- Lowering

class Monad m => MonadRun m where
  withRun :: ((forall r . m r -> r) -> m a) -> m a

instance MonadRun ((->) a) where
  withRun b a = b ($ a) a

instance MonadRun Identity where
  withRun b = b runIdentity


-- Construction

fn :: MonadRun m => (a -> m r) -> m (a -> r)
fn b = withRun (\ run -> pure (run . b))


-- Defaults

distributeRun :: (MonadRun f, Functor g) => g (f a) -> f (g a)
distributeRun g = withRun (\ run -> pure (run <$> g))
