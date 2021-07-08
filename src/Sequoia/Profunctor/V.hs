module Sequoia.Profunctor.V
( V(..)
) where

import Data.Profunctor

newtype V s a b = V { runV :: s -> b }
  deriving (Functor)

instance Profunctor (V s) where
  dimap _ g = V . rmap g . runV

instance Costrong (V s) where
  unfirst  = V . fmap fst . runV
  unsecond = V . fmap snd . runV

instance Choice (V s) where
  left'  = V . fmap Left  . runV
  right' = V . fmap Right . runV

instance Closed (V s) where
  closed = V . fmap const . runV
