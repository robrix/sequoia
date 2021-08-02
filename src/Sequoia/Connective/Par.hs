module Sequoia.Connective.Par
( -- * Negative disjunction
  type (⅋)(..)
) where

import Sequoia.Disjunction
import Sequoia.Polarity

-- Negative disjunction

newtype a ⅋ b = Par { getPar :: forall r . (a -> r, b -> r) -> r }
  deriving (Functor)

infixr 7 ⅋

instance (Neg a, Neg b) => Polarized N (a ⅋ b) where

instance Foldable ((⅋) f) where
  foldMap = foldMapDisj

instance Traversable ((⅋) f) where
  traverse = traverseDisj

instance Disj (⅋) where
  inl l = Par $ \ k -> fst k l
  inr r = Par $ \ k -> snd k r
  ifl <--> ifr = \ par -> getPar par (ifl, ifr)
