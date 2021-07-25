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
  fmap f i = ItT (\ k r -> getItT i (k . f) (r . fmap (fmap f)))

instance Applicative (ItT r m) where
  pure = doneItT
  (<*>) = ap

instance Monad (ItT r m) where
  i >>= f = go i where go i = ItT (\ k r -> runItT (runItT k r . f) (r . fmap go) i)

instance MonadTrans (ItT r) where
  lift m = ItT (const . (m >>=))


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
