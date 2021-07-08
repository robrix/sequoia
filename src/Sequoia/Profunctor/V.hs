module Sequoia.Profunctor.V
( V(..)
) where

newtype V s a b = V { runV :: s -> b }
  deriving (Functor)
