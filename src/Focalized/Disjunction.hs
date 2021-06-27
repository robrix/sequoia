module Focalized.Disjunction
( -- * Negative disjunction
  type (⅋)(..)
  -- * Positive disjunction
, type (⊕)(..)
  -- * Disjunction
, Disj(..)
, foldMapDisj
, traverseDisj
, bifoldMapDisj
, bimapDisj
, bitraverseDisj
) where

import Focalized.Polarity

-- Negative disjunction

newtype a ⅋ b = Par (forall r . (a -> r) -> (b -> r) -> r)
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
  exlr ifl ifr (Par run) = run ifl ifr


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
  exlr ifl ifr = \case
    InL l -> ifl l
    InR r -> ifr r


-- Disjunction

class Disj d where
  inl :: a -> (a `d` b)
  inr :: b -> (a `d` b)
  exlr :: (a -> r) -> (b -> r) -> ((a `d` b) -> r)

instance Disj Either where
  inl = Left
  inr = Right
  exlr = either

foldMapDisj :: (Disj p, Monoid m) => (b -> m) -> (a `p` b) -> m
foldMapDisj = exlr (const mempty)

traverseDisj :: (Disj p, Applicative m) => (b -> m b') -> (a `p` b) -> m (a `p` b')
traverseDisj f = exlr (pure . inl) (fmap inr . f)

bifoldMapDisj :: Disj p => (a -> m) -> (b -> m) -> (a `p` b -> m)
bifoldMapDisj = exlr

bimapDisj :: Disj p => (a -> a') -> (b -> b') -> (a `p` b -> a' `p` b')
bimapDisj f g = exlr (inl . f) (inr . g)

bitraverseDisj :: (Disj p, Functor m) => (a -> m a') -> (b -> m b') -> (a `p` b -> m (a' `p` b'))
bitraverseDisj f g = exlr (fmap inl . f) (fmap inr . g)
