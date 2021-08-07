{-# LANGUAGE TypeFamilies #-}
module Sequoia.Connective.Additive
( -- * Duals
  elimWith
, elimSum
  -- * Negative truth
, Top(..)
  -- * Positive falsity
, Zero
, absurdP
  -- * Negative conjunction
, type (&)(..)
  -- * Elimination
, runWith
  -- * Positive disjunction
, type (⊕)(..)
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
import Sequoia.Connective.Negation
import Sequoia.Disjunction
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Duals

elimWith :: a & b -> Negate e a r ⊕ Negate e b r -> r
elimWith = flip ((. exl) . (•-) <--> (. exr) . (•-))

elimSum :: a ⊕ b -> a ¬ r & b ¬ r -> r
elimSum = (. exl) . flip (•¬) <--> (. exr) . flip (•¬)


-- Adjunctions

instance Biadjunction (⊕) (&) where
  bileftAdjunct = bileftAdjunctDisjConj
  birightAdjunct = birightAdjunctDisjConj

instance Adjunction (Join (⊕)) (Join (&)) where
  leftAdjunct = leftAdjunctBiadjunction
  rightAdjunct = rightAdjunctBiadjunction


-- Negative truth

data Top = Top
  deriving (Eq, Ord, Show)

instance Polarized N Top where


-- Positive falsity

data Zero

instance Polarized P Zero where

absurdP :: Zero -> a
absurdP = \case


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

instance Bidistributive (&) where
  bidistribute = bidistributeConj
  bicollect = bicollectConj

instance Birepresentable (&) where
  type Birep (&) = Either () ()
  bitabulate = bitabulateConj
  biindex = biindexConj


-- Elimination

runWith :: Either (a • r) (b • r) -> (a & b) • r
runWith e = K (\ (With r) -> r • e)


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

instance Bifoldable (⊕) where
  bifoldMap = bifoldMapDisj

instance Bifunctor (⊕) where
  bimap = bimapDisj

instance Bitraversable (⊕) where
  bitraverse = bitraverseDisj
