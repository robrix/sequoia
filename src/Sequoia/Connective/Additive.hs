{-# LANGUAGE TypeFamilies #-}
module Sequoia.Connective.Additive
( -- * Duals
  elimWith
, elimSum
  -- * Negative conjunction
, type (&)(..)
  -- * Elimination
, runWith
  -- * Positive disjunction
, type (⊕)(..)
  -- * Connectives
, module Sequoia.Connective.Top
, module Sequoia.Connective.Zero
) where

import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Sequoia.Bidistributive
import Sequoia.Birepresentable
import Sequoia.Conjunction
import Sequoia.Connective.Negation
import Sequoia.Connective.Top
import Sequoia.Connective.Zero
import Sequoia.Disjunction
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Duals

elimWith :: a & b -> Negate e a r ⊕ Negate e b r -> r
elimWith = flip ((. exl) . (•-) <--> (. exr) . (•-))

elimSum :: a ⊕ b -> a ¬ r & b ¬ r -> r
elimSum = (. exl) . flip (•¬) <--> (. exr) . flip (•¬)


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
