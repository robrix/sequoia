module Sequoia.Profunctor.Context
( C(..)
) where

newtype C e r = C { runC :: e -> r }
  deriving (Applicative, Functor, Monad)
