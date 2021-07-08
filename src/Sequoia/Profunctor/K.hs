module Sequoia.Profunctor.K
( K(..)
) where

newtype K r a b = K { runK :: a -> r }
  deriving (Functor)
