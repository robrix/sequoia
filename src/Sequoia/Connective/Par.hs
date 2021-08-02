module Sequoia.Connective.Par
( -- * Negative disjunction
  type (⅋)(..)
  -- * Elimination
, runPar
) where

import Sequoia.Conjunction
import Sequoia.Disjunction
import Sequoia.Polarity

-- Negative disjunction

newtype a ⅋ b = Par (forall r . (a -> r, b -> r) -> r)
  deriving (Functor)

infixr 7 ⅋

instance (Neg a, Neg b) => Polarized N (a ⅋ b) where

instance Foldable ((⅋) f) where
  foldMap = foldMapDisj

instance Traversable ((⅋) f) where
  traverse = traverseDisj

instance Disj (⅋) where
  inl l = Par (`exl` l)
  inr r = Par (`exr` r)
  ifl <--> ifr = runPar (ifl >--< ifr)


-- Elimination

runPar :: (a -> r, b -> r) -> (a ⅋ b -> r)
runPar e (Par r) = r e
