module Sequoia.Disjunction
( -- * Disjunction
  Disj(..)
, _inl
, _inr
, exlD
, exrD
, mirrorDisj
  -- * Generalizations
, coerceDisj
, leftDisj
, rightDisj
, (+++)
, (|||)
, unleftDisj
, unrightDisj
  -- * Defaults
, foldMapDisj
, traverseDisj
, bifoldMapDisj
, bimapDisj
, bitraverseDisj
  -- * Lifted injections
, inlF
, inrF
, inlK
, inrK
, inlL
, inrL
, inlR
, inrR
) where

import Control.Category (Category, (>>>))
import Data.Functor.Contravariant
import Data.Profunctor
import Sequoia.Bijection
import Sequoia.Profunctor.Diagonal

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

mirrorDisj :: Disj d => a `d` b -> b `d` a
mirrorDisj = inr <--> inl


-- Generalizations

coerceDisj :: (Disj c1, Disj c2) => a `c1` b -> a `c2` b
coerceDisj = inl <--> inr

leftDisj :: (Disj d, Choice p) => p a b -> p (d a c) (d b c)
leftDisj = dimap coerceDisj coerceDisj . left'

rightDisj :: (Disj d, Choice p) => p a b -> p (d c a) (d c b)
rightDisj = dimap coerceDisj coerceDisj . right'

(+++) :: (Choice p, Category p, Disj c) => a1 `p` b1 -> a2 `p` b2 -> (a1 `c` a2) `p` (b1 `c` b2)
f +++ g = leftDisj f >>> rightDisj g

infixr 2 +++

(|||) :: (Choice p, Category p, Disj c, Codiagonal p) => a1 `p` b -> a2 `p` b -> (a1 `c` a2) `p` b
f ||| g = f +++ g >>> lmap coerceDisj dedup

infixr 2 |||

unleftDisj :: (Disj d, Cochoice p) => p (d a c) (d b c) -> p a b
unleftDisj = unleft . dimap coerceDisj coerceDisj

unrightDisj :: (Disj d, Cochoice p) => p (d c a) (d c b) -> p a b
unrightDisj = unright . dimap coerceDisj coerceDisj


-- Defaults

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

inlF :: (Functor f, Disj d) => f a -> f (a `d` b)
inrF :: (Functor f, Disj d) => f b -> f (a `d` b)
inlF = fmap inl
inrF = fmap inr

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
