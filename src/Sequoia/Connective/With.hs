module Sequoia.Connective.With
( -- * Negative conjunction
  type (&)(..)
  -- * Elimination
, runWith
) where

import Sequoia.Conjunction
import Sequoia.Disjunction
import Sequoia.Polarity

-- Negative conjunction

newtype a & b = With (forall r . Either (a -> r) (b -> r) -> r)
  deriving (Functor)

infixr 6 &

instance (Neg a, Neg b) => Polarized N (a & b) where

instance Foldable ((&) f) where
  foldMap = foldMapConj

instance Traversable ((&) f) where
  traverse = traverseConj

instance Conj (&) where
  a >--< b = With (($ a) <--> ($ b))
  exl = runWith (inl id)
  exr = runWith (inr id)


-- Elimination

runWith :: Either (a -> r) (b -> r) -> (a & b -> r)
runWith e (With r) = r e
