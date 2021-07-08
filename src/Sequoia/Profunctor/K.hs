module Sequoia.Profunctor.K
( K(..)
) where

import Data.Profunctor

newtype K r a b = K { runK :: a -> r }
  deriving (Functor)

instance Profunctor (K r) where
  dimap f _ = K . lmap f . runK

instance Strong (K r) where
  first'  = K . lmap fst . runK
  second' = K . lmap snd . runK

instance Cochoice (K r) where
  unleft  = K . lmap Left  . runK
  unright = K . lmap Right . runK
