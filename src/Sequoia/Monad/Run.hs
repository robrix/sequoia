{-# LANGUAGE FunctionalDependencies #-}
-- | Lowering (running) “pure” monads to a value.
module Sequoia.Monad.Run
( -- * Lowering
  MonadRun(..)
  -- * CPS lowering
, MonadRunK(..)
  -- * Construction
, fn
, inKM
, cont
, contK
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

instance MonadRun ((•) a) where
  withRun b = K (\ a -> b (• a) • a)


-- CPS lowering

class Monad m => MonadRunK r m | m -> r where
  withRunK :: ((forall x . x • r -> m x -> r) -> m a) -> m a


-- Construction

fn :: MonadRun m => (a -> m r) -> m (a -> r)
fn = distributeRun

inKM :: MonadRun m => (a -> m r) -> m (a • r)
inKM = fmap K . fn

cont :: MonadRun m => ((forall b . (b -> m r) -> b • r) -> m a) -> m a
cont f = withRun (\ run -> f (K . (run .)))

contK :: MonadRunK r m => ((forall b . (b -> m r) -> b • r) -> m a) -> m a
contK f = withRunK (\ run -> f (K . (run idK .)))


-- Defaults

withRunWithRep :: Representable f => Rep f -> ((forall r . f r -> r) -> f a) -> f a
withRunWithRep r b = b (`index` r)

distributeRun :: (MonadRun f, Functor g) => g (f a) -> f (g a)
distributeRun = collectRun id

collectRun :: (MonadRun f, Functor g) => (a -> f b) -> g a -> f (g b)
collectRun f g = withRun (\ run -> pure (run . f <$> g))
