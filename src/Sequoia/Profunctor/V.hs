module Sequoia.Profunctor.V
( V(..)
) where

import Data.Functor.Const
import Data.Profunctor
import Data.Profunctor.Sieve

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

instance Sieve (V s) ((->) s) where
  sieve = const . runV

instance Cosieve (V s) (Const s) where
  cosieve = lmap getConst . runV
