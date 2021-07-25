module Sequoia.Monad.Trans.It
( -- * Iteratees
  ItT(..)
  -- * Construction
, itT
, doneItT
  -- * Elimination
, runItT
, foldItT
) where

import Control.Monad (ap)
import Control.Monad.Trans.Class

-- Iteratees

newtype ItT r m a = ItT { getItT :: forall s . (a -> m s) -> ((r -> ItT r m a) -> m s) -> m s }

instance Functor (ItT r m) where
  fmap f r = ItT (\ a k -> getItT r (a . f) (k . fmap (fmap f)))

instance Applicative (ItT r m) where
  pure = doneItT
  (<*>) = ap

instance Monad (ItT r m) where
  r >>= f = go r where go r = ItT (\ a k -> runItT (runItT a k . f) (k . fmap go) r)

instance MonadTrans (ItT r) where
  lift m = ItT (\ a _ -> m >>= a)


-- Construction

itT :: (r -> ItT r m a) -> ItT r m a
itT k = ItT (const ($ k))

doneItT :: a -> ItT r m a
doneItT a = ItT (const . ($ a))


-- Elimination

runItT :: (a -> m s) -> ((r -> ItT r m a) -> m s) -> (ItT r m a -> m s)
runItT p k i = getItT i p k

foldItT :: (a -> m s) -> ((r -> m s) -> m s) -> (ItT r m a -> m s)
foldItT p k = go where go = runItT p (k . fmap go)
