{-# LANGUAGE ConstraintKinds #-}
module Sequoia.Disjunction
( -- * Disjunction
  Disj
, DisjIn(..)
, DisjEx(..)
, _inl
, _inr
, _inlK
, _inrK
, exlD
, exrD
, (<••>)
, (<∘∘>)
, mirrorDisj
, cocurryDisj
, councurryDisj
, coapDisj
  -- * Generalizations
, coerceDisj
, leftDisj
, rightDisj
, (+++)
, (|||)
, dedupDisj
, unleftDisj
, unrightDisj
, prismDisj
  -- * Defaults
, foldMapDisj
, fmapDisj
, traverseDisj
, bifoldMapDisj
, bimapDisj
, bitraverseDisj
, bisequenceDisj
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
import Data.Profunctor.Rep
import Data.Profunctor.Sieve
import Fresnel.Lens
import Fresnel.Prism
import Sequoia.Bifunctor.Sum
import Sequoia.Profunctor.Command
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Diagonal
import Sequoia.Profunctor.Value

-- Disjunction

type Disj d = (DisjIn d, DisjEx d)

class DisjIn d where
  inl :: a -> (a `d` b)
  inr :: b -> (a `d` b)

instance DisjIn Either where
  inl = Left
  inr = Right

instance DisjIn (+) where
  inl = inSl
  inr = inSr

class DisjEx d where
  (<-->) :: (a -> r) -> (b -> r) -> (a `d` b -> r)
  infixr 3 <-->

instance DisjEx Either where
  (<-->) = either

instance DisjEx (+) where
  (<-->) = runS

_inl :: Disj d => Prism (a `d` b) (a' `d` b) a a'
_inl = prism inl (inr <--> inl . inr)

_inr :: Disj d => Prism (a `d` b) (a `d` b') b b'
_inr = prism inr (inl . inl <--> inr)

_inlK :: (Disj d, Representable k) => Lens (k (a `d` b) r) (k (a' `d` b) r) (k a r) (k a' r)
_inlK = lens inlL (\ ab a' -> tabulate (sieve a' <--> sieve ab . inr))

_inrK :: (Disj d, Representable k) => Lens (k (a `d` b) r) (k (a `d` b') r) (k b r) (k b' r)
_inrK = lens inrL (\ ab a' -> tabulate (sieve ab . inl <--> sieve a'))

exlD :: Disj d => a `d` b -> Maybe a
exlD = Just <--> const Nothing

exrD :: Disj d => a `d` b -> Maybe b
exrD = const Nothing <--> Just

(<••>) :: (Disj d, Continuation k) => a `k` r -> b `k` r -> (a `d` b) `k` r
a <••> b = inK ((a •) <--> (b •))

infixr 3 <••>

(<∘∘>) :: (Disj d, Value v) => (e `v` a -> r) -> (e `v` b -> r) -> (e `v` (a `d` b) -> e ==> r)
(l <∘∘> r) ab = C ((l <--> r) . bisequenceDisjV ab)

infixr 3 <∘∘>

bisequenceDisjV :: (Disj d, Value v) => e `v` (a `d` b) -> e -> (e `v` a) `d` (e `v` b)
bisequenceDisjV = fmap (bimapDisj (inV . pure) (inV . pure)) . flip (∘)

mirrorDisj :: Disj d => a `d` b -> b `d` a
mirrorDisj = inr <--> inl

cocurryDisj :: (Disj d, Continuation k) => (c -> ((b `d` a) `k` r) `k` r) -> ((c, b `k` r) -> (a `k` r) `k` r)
cocurryDisj f (c, b) = inK (\ k -> f c • (b <••> k))

councurryDisj :: (DisjIn d, Continuation k) => ((c, b `k` r) -> (a `k` r) `k` r) -> c -> ((b `d` a) `k` r) `k` r
councurryDisj f c = inK (\ k -> f (c, inlL k) • inrL k)

coapDisj :: (DisjIn d, Continuation k) => c -> (((c, b `k` r) `d` b) `k` r) `k` r
coapDisj c = inK (\ k -> inlL k • (c, inrL k))


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
f ||| g = f +++ g >>> dedupDisj

infixr 2 |||

dedupDisj :: (Codiagonal p, Disj d) => (a `d` a) `p` a
dedupDisj = lmap coerceDisj dedup

unleftDisj :: (Disj d, Cochoice p) => p (d a c) (d b c) -> p a b
unleftDisj = unleft . dimap coerceDisj coerceDisj

unrightDisj :: (Disj d, Cochoice p) => p (d c a) (d c b) -> p a b
unrightDisj = unright . dimap coerceDisj coerceDisj


prismDisj :: Disj d => (b -> t) -> (s -> t `d` a) -> Prism s t a b
prismDisj inj = prism inj . (coerceDisj .)


-- Defaults

foldMapDisj :: (Disj p, Monoid m) => (b -> m) -> (a `p` b) -> m
foldMapDisj = (const mempty <-->)

fmapDisj :: Disj p => (b -> b') -> (a `p` b -> a `p` b')
fmapDisj g = inl <--> inr . g

traverseDisj :: (Disj p, Applicative m) => (b -> m b') -> (a `p` b) -> m (a `p` b')
traverseDisj f = pure . inl <--> inrF . f

bifoldMapDisj :: Disj p => (a -> m) -> (b -> m) -> (a `p` b -> m)
bifoldMapDisj = (<-->)

bimapDisj :: Disj p => (a -> a') -> (b -> b') -> (a `p` b -> a' `p` b')
bimapDisj = (+++)

bitraverseDisj :: (Disj p, Functor m) => (a -> m a') -> (b -> m b') -> (a `p` b -> m (a' `p` b'))
bitraverseDisj f g = inlF . f <--> inrF . g

bisequenceDisj :: (Disj d, Functor f) => f a `d` f b -> f (a `d` b)
bisequenceDisj = inlF <--> inrF


-- Lifted injections

inlF :: (Functor f, DisjIn d) => f a -> f (a `d` b)
inrF :: (Functor f, DisjIn d) => f b -> f (a `d` b)
inlF = fmap inl
inrF = fmap inr

inlK :: (Contravariant k, DisjIn d) => k (a `d` b) -> k a
inrK :: (Contravariant k, DisjIn d) => k (a `d` b) -> k b
inlK = contramap inl
inrK = contramap inr

inlL :: (Profunctor p, DisjIn d) => p (a `d` b) r -> p a r
inrL :: (Profunctor p, DisjIn d) => p (a `d` b) r -> p b r
inlL = lmap inl
inrL = lmap inr

inlR :: (Profunctor p, DisjIn d) => p l a -> p l (a `d` b)
inrR :: (Profunctor p, DisjIn d) => p l b -> p l (a `d` b)
inlR = rmap inl
inrR = rmap inr
