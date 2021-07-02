module Focalized.Connective.Sum
( -- * Positive disjunction
  type (⊕)(..)
) where

import Focalized.Disjunction
import Focalized.Polarity

-- Positive disjunction

data a ⊕ b
  = InL !a
  | InR !b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 6 ⊕

instance (Pos a, Pos b) => Polarized P (a ⊕ b)

instance Disj (⊕) where
  inl = InL
  inr = InR
  ifl <--> ifr = \case
    InL l -> ifl l
    InR r -> ifr r
