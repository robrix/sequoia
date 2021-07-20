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
, ala
, alaf
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
from o = withIso o (flip (<->))

constant :: a -> (a -> b) <-> b
constant a = ($ a) <-> const

involuted :: (a -> a) -> a <-> a
involuted f = f <-> f

flipped :: Iso (a -> b -> c) (a' -> b' -> c') (b -> a -> c) (b' -> a' -> c')
flipped = flip <-> flip

curried :: Iso ((a, b) -> c) ((a', b') -> c') (a -> b -> c) (a' -> b' -> c')
curried = curry <-> uncurry

uncurried :: Iso (a -> b -> c) (a' -> b' -> c') ((a, b) -> c) ((a', b') -> c')
uncurried = uncurry <-> curry

swapped :: Iso (a, b) (a', b') (b, a) (b', a')
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
au o f = withIso o (\ v r -> v <$> f r)

auf :: (Functor f, Functor g) => Iso s t a b -> ((f t -> g s) -> (f b -> g a))
auf o f b = withIso o (\ v r -> v <$> f (r <$> b))

xplat :: Functor g => Iso s t a b -> ((s -> a) -> g b) -> g t
xplat o = au (from o)

xplatf :: (Functor f, Functor g) => Iso s t a b -> ((f a -> g b) -> (f s -> g t))
xplatf o = auf (from o)

ala :: (Functor f, Coercible s a, Coercible b t) => (a -> s) -> ((b -> t) -> f s) -> f a
ala _ f = coerce <$> f coerce

alaf :: (Functor f, Functor g, Coercible s a, Coercible b t) => (a -> s) -> ((f t -> g s) -> (f b -> g a))
alaf _ f b = coerce <$> f (coerce <$> b)


-- Coercion

coerced :: (Coercible s a, Coercible t b) => Iso s t a b
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
coercedTo   :: Coercible t b => (s -> a) -> Iso s t a b
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
coercedFrom :: Coercible s a => (b -> t) -> Iso s t a b
coercedFrom = (coerce <->)


-- Representable (covariant)

tabulated :: (Co.Representable f, Co.Representable g) => Iso (Co.Rep f -> a) (Co.Rep g -> b) (f a) (g b)
tabulated = Co.tabulate <-> Co.index


-- Representable (contravariant)

contratabulated :: (Contra.Representable f, Contra.Representable g) => Iso (a -> Contra.Rep f) (b -> Contra.Rep g) (f a) (g b)
contratabulated = Contra.tabulate <-> Contra.index


-- (Co-)representable (profunctorial)

protabulated :: (Pro.Representable p, Pro.Representable q) => Iso (a -> Pro.Rep p b) (a' -> Pro.Rep q b') (a `p` b) (a' `q` b')
protabulated = Pro.tabulate <-> sieve

cotabulated :: (Pro.Corepresentable p, Pro.Corepresentable q) => Iso (Pro.Corep p a -> b) (Pro.Corep q a' -> b') (a `p` b) (a' `q` b')
cotabulated = Pro.cotabulate <-> cosieve


-- Adjunction

adjuncted :: (Co.Adjunction f u, Co.Adjunction f' u') => Iso (f a -> b) (f' a' -> b') (a -> u b) (a' -> u' b')
adjuncted = Co.leftAdjunct <-> Co.rightAdjunct

contraadjuncted :: (Contra.Adjunction f u, Contra.Adjunction f' u') => Iso (a -> f b) (a' -> f' b') (b -> u a) (b' -> u' a')
contraadjuncted = Contra.leftAdjunct <-> Contra.rightAdjunct


-- Functor

fmapping :: (Functor f, Functor g) => Iso s t a b -> Iso (f s) (g t) (f a) (g b)
fmapping a = fmap (view a) <-> fmap (review a)

contramapping :: (Contravariant f, Contravariant g) => Iso s t a b -> Iso (f a) (g b) (f s) (g t)
contramapping a = contramap (view a) <-> contramap (review a)


-- Bifunctor

bimapping :: (Bifunctor p, Bifunctor q) => Iso s t a b -> Iso s' t' a' b' -> Iso (p s s') (q t t') (p a a') (q b b')
bimapping a b = bimap (view a) (view b) <-> bimap (review a) (review b)

firsting :: (Bifunctor p, Bifunctor q) => Iso s t a b -> Iso (p s x) (q t y) (p a x) (q b y)
firsting a = first (view a) <-> first (review a)

seconding :: (Bifunctor p, Bifunctor q) => Iso s t a b -> Iso (p x s) (q y t) (p x a) (q y b)
seconding b = second (view b) <-> second (review b)


-- Profunctor

dimapping :: (Profunctor p, Profunctor q) => Iso s t a b -> Iso s' t' a' b' -> Iso (p a s') (q b t') (p s a') (q t b')
dimapping a b = dimap (view a) (view b) <-> dimap (review a) (review b)

lmapping :: (Profunctor p, Profunctor q) => Iso s t a b -> Iso (p a x) (q b y) (p s x) (q t y)
lmapping a = lmap (view a) <-> lmap (review a)

rmapping :: (Profunctor p, Profunctor q) => Iso s t a b -> Iso (p x s) (q y t) (p x a) (q y b)
rmapping b = rmap (view b) <-> rmap (review b)
