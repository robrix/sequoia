module Sequoia.Profunctor.V
( V(..)
) where

import Data.Profunctor

newtype V s a b = V { runV :: s -> b }
  deriving (Functor)

instance Profunctor (V s) where
  dimap _ g = V . rmap g . runV
