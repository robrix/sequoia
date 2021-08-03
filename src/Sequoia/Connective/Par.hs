module Sequoia.Connective.Par
( -- * Negative disjunction
  type (⅋)(..)
  -- * Elimination
, runPar
) where

import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Sequoia.Conjunction
import Sequoia.Disjunction
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Negative disjunction

newtype a ⅋ b = Par (forall r . (a • r, b • r) • r)

infixr 7 ⅋

instance (Neg a, Neg b) => Polarized N (a ⅋ b) where

instance Foldable ((⅋) f) where
  foldMap = foldMapDisj

instance Functor ((⅋) f) where
  fmap = fmapDisj

instance Traversable ((⅋) f) where
  traverse = traverseDisj

instance Disj (⅋) where
  inl l = Par (exlL (dn l))
  inr r = Par (exrL (dn r))
  ifl <--> ifr = (runPar (K ifl >--< K ifr) •)

instance Bifoldable (⅋) where
  bifoldMap = bifoldMapDisj

instance Bifunctor (⅋) where
  bimap = bimapDisj

instance Bitraversable (⅋) where
  bitraverse = bitraverseDisj


-- Elimination

runPar :: (a • r, b • r) -> (a ⅋ b) • r
runPar e = K (\ (Par r) -> r • e)
