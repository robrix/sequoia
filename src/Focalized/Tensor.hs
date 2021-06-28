module Focalized.Tensor
( -- * Positive conjunction
  type (⊗)(..)
) where

import Focalized.Conjunction
import Focalized.Polarity

-- Positive conjunction

data a ⊗ b = !a :⊗ !b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 7 ⊗, :⊗

instance (Pos a, Pos b) => Polarized P (a ⊗ b) where

instance Conj (⊗) where
  inlr = (:⊗)
  exl (l :⊗ _) = l
  exr (_ :⊗ r) = r
