module Focalized.Connective.Par
( -- * Negative disjunction
  type (⅋)(..)
) where

import Focalized.Disjunction
import Focalized.Polarity

-- Negative disjunction

newtype a ⅋ b = Par { getPar :: forall r . (a -> r) -> (b -> r) -> r }
  deriving (Functor)

infixr 7 ⅋

instance (Neg a, Neg b) => Polarized N (a ⅋ b) where

instance Foldable ((⅋) f) where
  foldMap = foldMapDisj

instance Traversable ((⅋) f) where
  traverse = traverseDisj

instance Disj (⅋) where
  inl l = Par $ \ ifl _ -> ifl l
  inr r = Par $ \ _ ifr -> ifr r
  ifl <--> ifr = \ par -> getPar par ifl ifr
