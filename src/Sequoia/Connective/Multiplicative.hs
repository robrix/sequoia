{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Connective.Multiplicative
( -- * Elimination
  elimPar
, elimTensor
  -- * Negative falsity
, Bottom(..)
  -- ** Elimination
, absurdNK
  -- * Positive truth
, One(..)
  -- * Negative disjunction
, type (⅋)(..)
  -- ** Elimination
, runPar
  -- * Positive conjunction
, type (⊗)(..)
) where

import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Functor.Adjunction
import Sequoia.Biadjunction
import Sequoia.Bidistributive
import Sequoia.Bifunctor.Join
import Sequoia.Birepresentable
import Sequoia.Conjunction
import Sequoia.Connective.Multiplicative.Unit
import Sequoia.Connective.Negation
import Sequoia.Disjunction
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Elimination

elimPar :: a ⅋ b -> Negate e a r ⊗ Negate e b r -> r
elimPar = (. exl) . flip (•-) <--> (. exr) . flip (•-)

elimTensor :: a ⊗ b -> a ¬ r ⅋ b ¬ r -> r
elimTensor = flip ((. exl) . (•) <--> (. exr) . (•))


-- Adjunction

instance Biadjunction (⅋) (⊗) where
  bileftAdjunct  = bileftAdjunctDisjConj
  birightAdjunct = birightAdjunctDisjConj

instance Adjunction (Join (⅋)) (Join (⊗)) where
  leftAdjunct  = leftAdjunctBiadjunction
  rightAdjunct = rightAdjunctBiadjunction


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

instance DisjIn (⅋) where
  inl l = Par (exlL (dn l))
  inr r = Par (exrL (dn r))

instance DisjEx (⅋) where
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


-- Positive conjunction

data a ⊗ b = !a :⊗ !b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 7 ⊗, :⊗

instance (Pos a, Pos b) => Polarized P (a ⊗ b) where

instance Conj (⊗) where
  (>--<) = (:⊗)
  exl (l :⊗ _) = l
  exr (_ :⊗ r) = r

instance Bifoldable (⊗) where
  bifoldMap = bifoldMapConj

instance Bifunctor (⊗) where
  bimap = bimapConj

instance Bitraversable (⊗) where
  bitraverse = bitraverseConj

instance Bidistributive (⊗) where
  bidistribute = bidistributeConj
  bicollect = bicollectConj

instance Birepresentable (⊗) where
  type Birep (⊗) = Either () ()
  bitabulate = bitabulateConj
  biindex = biindexConj
