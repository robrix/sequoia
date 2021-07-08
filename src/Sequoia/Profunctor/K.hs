module Sequoia.Profunctor.K
( K(..)
) where

import Data.Profunctor

newtype K r a b = K { runK :: a -> r }
  deriving (Functor)

instance Profunctor (K r) where
  dimap f _ = K . lmap f . runK
