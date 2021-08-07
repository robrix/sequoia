{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Connective.Multiplicative
( -- * Elimination
  elimPar
, elimTensor
  -- * Negative falsity
, Bottom(..)
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
import Data.Distributive
import Data.Functor.Adjunction
import Data.Functor.Identity
import Data.Functor.Rep
import Sequoia.Biadjunction
import Sequoia.Bidistributive
import Sequoia.Bifunctor.Join
import Sequoia.Birepresentable
import Sequoia.Conjunction
import Sequoia.Connective.Negation
import Sequoia.Disjunction
import Sequoia.Nulladjunction
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Elimination

elimPar :: a ⅋ b -> Negate e a r ⊗ Negate e b r -> r
elimPar = (. exl) . flip (•-) <--> (. exr) . flip (•-)

elimTensor :: a ⊗ b -> a ¬ r ⅋ b ¬ r -> r
elimTensor = flip ((. exl) . (•¬) <--> (. exr) . (•¬))


-- Adjunction

instance Biadjunction (⅋) (⊗) where
  bileftAdjunct  = bileftAdjunctDisjConj
  birightAdjunct = birightAdjunctDisjConj

instance Adjunction (Join (⅋)) (Join (⊗)) where
  leftAdjunct  = leftAdjunctBiadjunction
  rightAdjunct = rightAdjunctBiadjunction

instance Adjunction Bottom One where
  leftAdjunct  f = One . f . Bottom
  rightAdjunct f = getOne . f . absurdN

instance Nulladjunction r e => Nulladjunction (Bottom r) (One e) where
  nullleftAdjunct f = One . nullleftAdjunct (f . Bottom)
  nullrightAdjunct f = nullrightAdjunct (getOne . f) . absurdN


-- Negative falsity

newtype Bottom r = Bottom { absurdN :: r }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity

instance Polarized N (Bottom r) where


-- Positive truth

newtype One e = One { getOne :: e }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad, Representable) via Identity

instance Polarized P (One e) where

instance Distributive One where
  distribute = One . fmap getOne
  collect f = One . fmap (getOne . f)


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
  bitabulate = bitabulateConj
  biindex = biindexConj
