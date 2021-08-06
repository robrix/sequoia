module Sequoia.Profunctor.Exp
( -- * Exponential functors
  Exp(..)
) where

import Sequoia.Profunctor

-- Exponential functors

newtype Exp r a b = Exp { runExp :: (b -> r) -> (a -> r) }

instance Profunctor (Exp r) where
  dimap f g = Exp . dimap (<<^ g) (<<^ f) . runExp

instance Functor (Exp r a) where
  fmap = rmap
