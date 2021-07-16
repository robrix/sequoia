module Sequoia.Connective.With
( -- * Negative conjunction
  type (&)(..)
) where

import Sequoia.Conjunction
import Sequoia.Polarity

-- Negative conjunction

newtype a & b = With (forall r . (a -> b -> r) -> r)
  deriving (Functor)

infixr 6 &

instance (Neg a, Neg b) => Polarized N (a & b) where

instance Foldable ((&) f) where
  foldMap = foldMapConj

instance Traversable ((&) f) where
  traverse = traverseConj

instance Conj (&) where
  a >--< b = With $ \ (>--<) -> a >--< b
  exl (With run) = run const
  exr (With run) = run (const id)
