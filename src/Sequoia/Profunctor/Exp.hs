module Sequoia.Profunctor.Exp
( -- * Exponential functors
  Exp(..)
) where

-- Exponential functors

newtype Exp r a b = Exp { runExp :: (b -> r) -> (a -> r) }
