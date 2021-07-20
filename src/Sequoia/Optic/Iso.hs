module Sequoia.Optic.Iso
( -- * Isos
  Iso
, Iso'
, type (<->)
  -- * Construction
, (<->)
, from
, constant
, involuted
, flipped
, curried
, uncurried
, swapped
, non
  -- * Elimination
, withIso
, under
, au
, auf
, xplat
, xplatf
  -- * Coercion
, coerced
, coercedFrom
, coercedTo
  -- * Representable (covariant)
, tabulated
  -- * Representable (contravariant)
, contratabulated
  -- * (Co-)representable (profunctorial)
, protabulated
, cotabulated
  -- * Adjunction
, adjuncted
, contraadjuncted
  -- * Functor
, fmapping
, contramapping
  -- * Bifunctor
, bimapping
, firsting
, seconding
  -- * Profunctor
, dimapping
, lmapping
, rmapping
) where

import           Control.Applicative (Alternative)
import           Control.Monad (guard)
import           Data.Bifunctor
import           Data.Coerce
import qualified Data.Functor.Adjunction as Co
import           Data.Functor.Contravariant
import qualified Data.Functor.Contravariant.Adjunction as Contra
import qualified Data.Functor.Contravariant.Rep as Contra
import qualified Data.Functor.Rep as Co
import           Data.Maybe (fromMaybe)
import           Data.Profunctor
import qualified Data.Profunctor.Rep as Pro
import           Data.Profunctor.Sieve
import           Data.Tuple (swap)
import           Sequoia.Optic.Getter
import           Sequoia.Optic.Optic
import           Sequoia.Optic.Review
import           Sequoia.Profunctor.Coexponential
import           Sequoia.Profunctor.Exchange

-- Isos

type Iso s t a b = forall p . Profunctor p => Optic p s t a b

type Iso' s a = Iso s s a a


type a <-> b = Iso' a b

infix 1 <->


-- Construction

(<->) :: (s -> a) -> (b -> t) -> Iso s t a b
(<->) = dimap


from :: Iso s t a b -> Iso b a t s
from b = review b <-> view b

constant :: a -> (a -> b) <-> b
constant a = ($ a) <-> const

involuted :: (a -> a) -> a <-> a
involuted f = f <-> f

flipped :: (a -> b -> c) <-> (b -> a -> c)
flipped = flip <-> flip

curried :: ((a, b) -> c) <-> (a -> b -> c)
curried = curry <-> uncurry

uncurried :: (a -> b -> c) <-> ((a, b) -> c)
uncurried = uncurry <-> curry

swapped :: (a, b) <-> (b, a)
swapped = swap <-> swap

non :: Eq a => a -> Maybe a <-> a
non a = fromMaybe a <-> select (/= a)

select :: Alternative f => (a -> Bool) -> (a -> f a)
select p a = a <$ guard (p a)


-- Elimination

withIso :: Iso s t a b -> (((s -> a) -> (b -> t) -> r) -> r)
withIso = withExchange . ($ idExchange)


under :: Iso s t a b -> (t -> s) -> (b -> a)
under = runCoexp . ($ idCoexp)


au :: Functor f => Iso s t a b -> (((b -> t) -> f s) -> f a)
au o f = view o <$> f (review o)

auf :: (Functor f, Functor g) => Iso s t a b -> ((f t -> g s) -> (f b -> g a))
auf o f b = view o <$> f (review o <$> b)

xplat :: Functor g => Iso s t a b -> ((s -> a) -> g b) -> g t
xplat o = au (from o)

xplatf :: (Functor f, Functor g) => Iso s t a b -> ((f a -> g b) -> (f s -> g t))
xplatf o = auf (from o)


-- Coercion

coerced :: Coercible a b => a <-> b
coerced = coerce <-> coerce

-- | Build a bidi coercion, taking a constructor for the type being built both to improve type inference and as documentation.
--
-- For example, given two newtypes @A@ and @B@ wrapping the same type, this expression:
--
-- @
-- 'coercedTo' B <<< 'coercedFrom' A
-- @
--
-- produces a bijection of type @A '<->' B@.
coercedTo   :: Coercible a b => (a -> b) -> a <-> b
coercedTo   = (<-> coerce)

-- | Build a bidi coercion, taking a constructor for the type being eliminated both to improve type inference and as documentation.
--
-- For example, given two newtypes @A@ and @B@ wrapping the same type, this expression:
--
-- @
-- 'coercedTo' B <<< 'coercedFrom' A
-- @
--
-- produces a bijection of type @A '<->' B@.
coercedFrom :: Coercible a b => (b -> a) -> a <-> b
coercedFrom = (coerce <->)


-- Representable (covariant)

tabulated :: Co.Representable f => (Co.Rep f -> a) <-> f a
tabulated = Co.tabulate <-> Co.index


-- Representable (contravariant)

contratabulated :: Contra.Representable f => (a -> Contra.Rep f) <-> f a
contratabulated = Contra.tabulate <-> Contra.index


-- (Co-)representable (profunctorial)

protabulated :: Pro.Representable p => (a -> Pro.Rep p b) <-> a `p` b
protabulated = Pro.tabulate <-> sieve

cotabulated :: Pro.Corepresentable p => (Pro.Corep p a -> b) <-> a `p` b
cotabulated = Pro.cotabulate <-> cosieve


-- Adjunction

adjuncted :: Co.Adjunction f u => (f a -> b) <-> (a -> u b)
adjuncted = Co.leftAdjunct <-> Co.rightAdjunct

contraadjuncted :: Contra.Adjunction f u => (a -> f b) <-> (b -> u a)
contraadjuncted = Contra.leftAdjunct <-> Contra.rightAdjunct


-- Functor

fmapping :: (Functor f, Functor g) => Iso s t a b -> Iso (f s) (g t) (f a) (g b)
fmapping a = fmap (view a) <-> fmap (review a)

contramapping :: (Contravariant f, Contravariant g) => Iso s t a b -> Iso (f a) (g b) (f s) (g t)
contramapping a = contramap (view a) <-> contramap (review a)


-- Bifunctor

bimapping :: Bifunctor p => Iso s t a b -> Iso s' t' a' b' -> Iso (p s s') (p t t') (p a a') (p b b')
bimapping a b = bimap (view a) (view b) <-> bimap (review a) (review b)

firsting :: Bifunctor p => Iso s t a b -> Iso (p s x) (p t y) (p a x) (p b y)
firsting a = first (view a) <-> first (review a)

seconding :: Bifunctor p => Iso s t a b -> Iso (p x s) (p y t) (p x a) (p y b)
seconding b = second (view b) <-> second (review b)


-- Profunctor

dimapping :: Profunctor p => (a <-> a') -> (b <-> b') -> (a `p` b) <-> (a' `p` b')
dimapping a b = dimap (review a) (view b) <-> dimap (view a) (review b)

lmapping :: Profunctor p => (a <-> a') -> (a `p` b) <-> (a' `p` b)
lmapping a = lmap (review a) <-> lmap (view a)

rmapping :: Profunctor p => (b <-> b') -> (a `p` b) <-> (a `p` b')
rmapping b = rmap (view b) <-> rmap (review b)
