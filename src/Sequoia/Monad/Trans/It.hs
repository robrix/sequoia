module Sequoia.Monad.Trans.It
( -- * Iteratees
  ItT(..)
) where

-- Iteratees

newtype ItT r m a = ItT { getItT :: forall s . (a -> s) -> ((r -> m (ItT r m a)) -> s) -> s }
