module Sequoia.Connective.With
( -- * Negative conjunction
  type (&)(..)
  -- * Elimination
, runWith
) where

import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Sequoia.Conjunction
import Sequoia.Disjunction
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Negative conjunction

newtype a & b = With (forall r . Either (a • r) (b • r) • r)

infixr 6 &

instance (Neg a, Neg b) => Polarized N (a & b) where

instance Foldable ((&) f) where
  foldMap = foldMapConj

instance Functor ((&) r) where
  fmap = fmapConj

instance Traversable ((&) f) where
  traverse = traverseConj

instance Conj (&) where
  a >--< b = With (dn a <••> dn b)
  exl = (runWith (inl idK) •)
  exr = (runWith (inr idK) •)

instance Bifoldable (&) where
  bifoldMap = bifoldMapConj

instance Bifunctor (&) where
  bimap = bimapConj

instance Bitraversable (&) where
  bitraverse = bitraverseConj


-- Elimination

runWith :: Either (a • r) (b • r) -> (a & b) • r
runWith e = K (\ (With r) -> r • e)
