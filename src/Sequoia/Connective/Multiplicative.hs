{-# LANGUAGE TypeFamilies #-}
module Sequoia.Connective.Multiplicative
( -- * Elimination
  elimPar
, elimTensor
  -- * Adjunction
, leftAdjunctParTensor
, rightAdjunctParTensor
  -- * Negative disjunction
, type (⅋)(..)
  -- ** Elimination
, runPar
  -- * Positive conjunction
, type (⊗)(..)
  -- * Connectives
, module Sequoia.Connective.Bottom
, module Sequoia.Connective.One
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
import Sequoia.Connective.Bottom
import Sequoia.Connective.Negation
import Sequoia.Connective.One
import Sequoia.Disjunction
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Elimination

elimPar :: a ⅋ b -> Negate e a r ⊗ Negate e b r -> r
elimPar = (. exl) . flip (•-) <--> (. exr) . flip (•-)

elimTensor :: a ⊗ b -> a ¬ r ⅋ b ¬ r -> r
elimTensor = flip ((. exl) . (•¬) <--> (. exr) . (•¬))


-- Adjunction

leftAdjunctParTensor :: (a ⅋ a -> b) -> (a -> b ⊗ b)
leftAdjunctParTensor f = f . inl >---< f . inr

rightAdjunctParTensor :: (a -> b ⊗ b) -> (a ⅋ a -> b)
rightAdjunctParTensor f = exl . f <--> exr . f

instance Biadjunction (⅋) (⊗) where
  bileftAdjunct  = bileftAdjunctDisjConj
  birightAdjunct = birightAdjunctDisjConj

instance Adjunction (Join (⅋)) (Join (⊗)) where
  leftAdjunct  f = Join . (f . Join . inl >---< f . Join . inr)
  rightAdjunct f = (exl . runJoin . f <--> exr . runJoin . f) . runJoin


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
  bitabulate f g = f (inl ()) >--< g (inr ())
  biindex p = const (exl p) `bimap` const (exr p)
