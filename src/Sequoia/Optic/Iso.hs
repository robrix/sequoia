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
, under
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

-- Isos

type Iso s t a b = forall p . Profunctor p => Optic p s t a b

type Iso' s a = Iso s s a a


type a <-> b = Iso' a b

infix 1 <->


-- Construction

(<->) :: (s -> a) -> (b -> t) -> Iso s t a b
(<->) = dimap


from :: Iso s t a b -> Iso b a t s
from b = (b <~) <-> (~> b)

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

under :: Iso s t a b -> (t -> s) -> (b -> a)
under = runCoexp . ($ idCoexp)


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

fmapping :: Functor f => (a <-> a') -> f a <-> f a'
fmapping a = fmap (~> a) <-> fmap (a <~)

contramapping :: Contravariant f => (a <-> a') -> f a <-> f a'
contramapping a = contramap (a <~) <-> contramap (~> a)


-- Bifunctor

bimapping :: Bifunctor p => (a <-> a') -> (b <-> b') -> (a `p` b) <-> (a' `p` b')
bimapping a b = bimap (~> a) (~> b) <-> bimap (a <~) (b <~)

firsting :: Bifunctor p => (a <-> a') -> (a `p` b) <-> (a' `p` b)
firsting a = first (~> a) <-> first (a <~)

seconding :: Bifunctor p => (b <-> b') -> (a `p` b) <-> (a `p` b')
seconding b = second (~> b) <-> second (b <~)


-- Profunctor

dimapping :: Profunctor p => (a <-> a') -> (b <-> b') -> (a `p` b) <-> (a' `p` b')
dimapping a b = dimap (a <~) (~> b) <-> dimap (~> a) (b <~)

lmapping :: Profunctor p => (a <-> a') -> (a `p` b) <-> (a' `p` b)
lmapping a = lmap (a <~) <-> lmap (~> a)

rmapping :: Profunctor p => (b <-> b') -> (a `p` b) <-> (a `p` b')
rmapping b = rmap (~> b) <-> rmap (b <~)
