module Sequoia.Monad.Trans.It
( -- * Iteratees
  ItT(..)
  -- * Construction
, itT
, doneItT
) where

-- Iteratees

newtype ItT r m a = ItT { getItT :: forall s . (a -> s) -> ((r -> m (ItT r m a)) -> s) -> s }


-- Construction

itT :: (r -> m (ItT r m a)) -> ItT r m a
itT k = ItT (const ($ k))

doneItT :: a -> ItT r m a
doneItT a = ItT (const . ($ a))
