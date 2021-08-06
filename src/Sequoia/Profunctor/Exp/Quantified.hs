module Sequoia.Profunctor.Exp.Quantified
( -- * Exponentials
  type (-->)(..)
) where

newtype a --> b = Exp { getExp :: forall r . (b -> r) -> (a -> r) }
  deriving (Functor)
