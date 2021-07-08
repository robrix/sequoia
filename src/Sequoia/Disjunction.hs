module Sequoia.Disjunction
( -- * Disjunction
  Disj(..)
, _inl
, _inr
, exlD
, exrD
, foldMapDisj
, traverseDisj
, bifoldMapDisj
, bimapDisj
, bitraverseDisj
  -- * Lifted injections
, inlK
, inrK
, inlL
, inrL
, inlR
, inrR
) where

import Data.Functor.Contravariant
import Data.Profunctor
import Sequoia.Bijection

-- Disjunction

class Disj d where
  inl :: a -> (a `d` b)
  inr :: b -> (a `d` b)
  (<-->) :: (a -> r) -> (b -> r) -> (a `d` b -> r)
  infix 3 <-->

instance Disj Either where
  inl = Left
  inr = Right
  (<-->) = either

_inl :: Disj d => Optic Prism (a `d` b) (a' `d` b) a a'
_inl = prism inl (inr <--> inl . inr)

_inr :: Disj d => Optic Prism (a `d` b) (a `d` b') b b'
_inr = prism inr (inl . inl <--> inr)

exlD :: Disj d => a `d` b -> Maybe a
exlD = Just <--> const Nothing

exrD :: Disj d => a `d` b -> Maybe b
exrD = const Nothing <--> Just

foldMapDisj :: (Disj p, Monoid m) => (b -> m) -> (a `p` b) -> m
foldMapDisj = (const mempty <-->)

traverseDisj :: (Disj p, Applicative m) => (b -> m b') -> (a `p` b) -> m (a `p` b')
traverseDisj f = pure . inl <--> fmap inr . f

bifoldMapDisj :: Disj p => (a -> m) -> (b -> m) -> (a `p` b -> m)
bifoldMapDisj = (<-->)

bimapDisj :: Disj p => (a -> a') -> (b -> b') -> (a `p` b -> a' `p` b')
bimapDisj f g = inl . f <--> inr . g

bitraverseDisj :: (Disj p, Functor m) => (a -> m a') -> (b -> m b') -> (a `p` b -> m (a' `p` b'))
bitraverseDisj f g = fmap inl . f <--> fmap inr . g


-- Lifted injections

inlK :: (Contravariant k, Disj d) => k (a `d` b) -> k a
inrK :: (Contravariant k, Disj d) => k (a `d` b) -> k b
inlK = contramap inl
inrK = contramap inr

inlL :: (Profunctor p, Disj d) => p (a `d` b) r -> p a r
inrL :: (Profunctor p, Disj d) => p (a `d` b) r -> p b r
inlL = lmap inl
inrL = lmap inr

inlR :: (Profunctor p, Disj d) => p l a -> p l (a `d` b)
inrR :: (Profunctor p, Disj d) => p l b -> p l (a `d` b)
inlR = rmap inl
inrR = rmap inr
