module Sequoia.Profunctor.Exp
( -- * Exponential functors
  Exp(..)
) where

import Data.Function ((&))
import Sequoia.Profunctor

-- Exponential functors

newtype Exp r a b = Exp { runExp :: (b -> r) -> (a -> r) }

instance Profunctor (Exp r) where
  dimap f g = Exp . dimap (<<^ g) (<<^ f) . runExp

instance Functor (Exp r a) where
  fmap = rmap

instance Applicative (Exp r a) where
  pure = Exp . (const .) . (&)
  Exp xf <*> Exp xa = Exp (\ k a -> xf (\ f -> xa (k . f) a) a)
