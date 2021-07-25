module Sequoia.Monad.Trans.It
( -- * Iteratees
  ItT(..)
, ItP(..)
  -- * Construction
, itT
, doneItT
  -- * Elimination
, runItT
, foldItT
  -- * Computation
, dimapItT
) where

import Control.Monad (ap)
import Control.Monad.Trans.Class
import Data.Profunctor

-- Iteratees

-- | Scott–encoded iteratee monad transformer, based loosely on the one in @trifecta@.
newtype ItT r m a = ItT { getItT :: forall s . (a -> m s) -> ((r -> ItT r m a) -> m s) -> m s }

instance Functor (ItT r m) where
  fmap f = go where go i = ItT (\ k r -> getItT i (k . f) (r . fmap go))

instance Applicative (ItT r m) where
  pure = doneItT
  (<*>) = ap

instance Monad (ItT r m) where
  i >>= f = go i where go i = ItT (\ k r -> runItT (runItT k r . f) (r . fmap go) i)

instance MonadTrans (ItT r) where
  lift m = ItT (const . (m >>=))


newtype ItP m r a = ItP { getItP :: ItT r m a }

instance Profunctor (ItP m) where
  dimap f g (ItP i) = ItP (dimapItT f g i)


-- Construction

itT :: (r -> ItT r m a) -> ItT r m a
itT r = ItT (const ($ r))

doneItT :: a -> ItT r m a
doneItT a = ItT (const . ($ a))


-- Elimination

runItT :: (a -> m s) -> ((r -> ItT r m a) -> m s) -> (ItT r m a -> m s)
runItT k r i = getItT i k r

foldItT :: (a -> m s) -> ((r -> m s) -> m s) -> (ItT r m a -> m s)
foldItT k r = go where go = runItT k (r . fmap go)


-- Computation

dimapItT :: (r' -> r) -> (a -> a') -> ItT r m a -> ItT r' m a'
dimapItT f g = go where go i = ItT (\ k r -> runItT (k . g) (r . (go .) . (. f)) i)
