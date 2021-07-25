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

-- Iteratees

newtype ItT r m a = ItT { getItT :: forall s . (a -> s) -> ((r -> m (ItT r m a)) -> s) -> s }

instance Functor m => Functor (ItT r m) where
  fmap f = foldItT (doneItT . f) itT

instance Functor m => Applicative (ItT r m) where
  pure = doneItT
  (<*>) = ap

instance Functor m => Monad (ItT r m) where
  m >>= f = foldItT f itT m


-- Construction

itT :: (r -> m (ItT r m a)) -> ItT r m a
itT k = ItT (const ($ k))

doneItT :: a -> ItT r m a
doneItT a = ItT (const . ($ a))


-- Elimination

runItT :: (a -> s) -> ((r -> m (ItT r m a)) -> s) -> (ItT r m a -> s)
runItT p k i = getItT i p k

foldItT :: Functor m => (a -> s) -> ((r -> m s) -> s) -> (ItT r m a -> s)
foldItT p k = go where go = runItT p (k . fmap (fmap go))
