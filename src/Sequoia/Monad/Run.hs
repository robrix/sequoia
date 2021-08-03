-- | Lowering (running) “pure” monads to a value.
module Sequoia.Monad.Run
( -- * Lowering
  MonadRun(..)
  -- * Construction
, fn
, inK
, cont
  -- * Defaults
, withRunWithRep
, distributeRun
, collectRun
) where

import Data.Functor.Identity
import Data.Functor.Rep
import Sequoia.Profunctor.Continuation

-- Lowering

class Monad m => MonadRun m where
  withRun :: ((forall r . m r -> r) -> m a) -> m a

instance MonadRun ((->) a) where
  withRun b a = b ($ a) a

instance MonadRun Identity where
  withRun b = b runIdentity


-- Construction

fn :: MonadRun m => (a -> m r) -> m (a -> r)
fn = distributeRun

inK :: MonadRun m => (a -> m r) -> m (a • r)
inK = fmap K . fn

cont :: MonadRun m => ((forall b . (b -> m r) -> b • r) -> m a) -> m a
cont f = withRun (\ run -> f (K . (run .)))


-- Defaults

withRunWithRep :: Representable f => Rep f -> ((forall r . f r -> r) -> f a) -> f a
withRunWithRep r b = b (`index` r)

distributeRun :: (MonadRun f, Functor g) => g (f a) -> f (g a)
distributeRun = collectRun id

collectRun :: (MonadRun f, Functor g) => (a -> f b) -> g a -> f (g b)
collectRun f g = withRun (\ run -> pure (run . f <$> g))
