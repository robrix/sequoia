module Sequoia.Connective.Multiplicative
( -- * Elimination
  elimPar
, elimTensor
  -- * Adjunction
, leftAdjunct
, rightAdjunct
  -- * Positive conjunction
, type (⊗)(..)
  -- * Connectives
, module Sequoia.Connective.Bottom
, module Sequoia.Connective.One
, module Sequoia.Connective.Par
) where

import Sequoia.Conjunction
import Sequoia.Connective.Bottom
import Sequoia.Connective.Negation
import Sequoia.Connective.One
import Sequoia.Connective.Par
import Sequoia.Disjunction
import Sequoia.Polarity

-- Elimination

elimPar :: a ⅋ b -> Negate e a r ⊗ Negate e b r -> r
elimPar = (. exl) . flip (•-) <--> (. exr) . flip (•-)

elimTensor :: a ⊗ b -> a ¬ r ⅋ b ¬ r -> r
elimTensor = flip ((. exl) . (•¬) <--> (. exr) . (•¬))


-- Adjunction

leftAdjunct :: (a ⅋ a -> b) -> (a -> b ⊗ b)
leftAdjunct f = f . inl >---< f . inr

rightAdjunct :: (a -> b ⊗ b) -> (a ⅋ a -> b)
rightAdjunct f = exl . f <--> exr . f


-- Positive conjunction

data a ⊗ b = !a :⊗ !b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 7 ⊗, :⊗

instance (Pos a, Pos b) => Polarized P (a ⊗ b) where

instance Conj (⊗) where
  (>--<) = (:⊗)
  exl (l :⊗ _) = l
  exr (_ :⊗ r) = r
