module Focalized.Disjunction
( -- * Disjunction
  Disj(..)
, exlD
, exrD
, foldMapDisj
, traverseDisj
, bifoldMapDisj
, bimapDisj
, bitraverseDisj
  -- * Lifted injections
, inlC
, inrC
, inlF
, inrF
, inlL
, inrL
, inlR
, inrR
) where

import Data.Functor.Contravariant
import Data.Profunctor

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

inlC :: (Contravariant f, Disj d) => f (a `d` b) -> f a
inrC :: (Contravariant f, Disj d) => f (a `d` b) -> f b
inlC = contramap inl
inrC = contramap inr

inlF :: (Functor f, Disj d) => f a -> f (a `d` b)
inrF :: (Functor f, Disj d) => f b -> f (a `d` b)
inlF = fmap inl
inrF = fmap inr

inlL :: (Profunctor p, Disj d) => p (a `d` b) r -> p a r
inrL :: (Profunctor p, Disj d) => p (a `d` b) r -> p b r
inlL = lmap inl
inrL = lmap inr

inlR :: (Profunctor p, Disj d) => p l a -> p l (a `d` b)
inrR :: (Profunctor p, Disj d) => p l b -> p l (a `d` b)
inlR = rmap inl
inrR = rmap inr
