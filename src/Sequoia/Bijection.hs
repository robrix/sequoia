{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Bijection
( -- * Bijections
  type (<->)
, Optic(..)
, Iso
, Lens
, Prism
  -- ** Elimination
, exBl
, exBr
, (<~)
, (~>)
, over
, under
  -- ** Construction
, (<->)
, from
, constant
, involuted
, flipped
, curried
, uncurried
, swapped
, non
, bij
  -- ** Coercion
, coerced
, coercedFrom
, coercedTo
  -- ** Representable
, tabulated
, contratabulated
  -- ** Adjunction
, adjuncted
, contraadjuncted
  -- ** Functor
, fmapping
, contramapping
  -- ** Bifunctor
, bimapping
, firsting
, seconding
  -- ** Profunctor
, dimapping
, lmapping
, rmapping
  -- * Tagged
, Tagged
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
import           Data.Tuple (swap)

-- Bijections

type a <-> b = Optic Iso a a b b

infix 1 <->


type OpticF c s t a b = forall p . c p => (a `p` b) -> (s `p` t)

newtype Optic c s t a b = Optic { runOptic :: OpticF c s t a b }


class Profunctor p => Iso p
instance Profunctor p => Iso p


class Strong p => Lens p
instance Strong p => Lens p


class Choice p => Prism p
instance Choice p => Prism p


-- Elimination

exBls :: c (Forget r) => Optic c s t a b -> (a -> r) -> (s -> r)
exBls b = runForget . runOptic b . Forget

exBl :: c (Forget a) => Optic c s t a b -> (s -> a)
exBl b = exBls b id

exBrs :: c Tagged => Optic c s t a b -> (t -> r) -> (b -> r)
exBrs b f = f . getTagged . runOptic b . Tagged

exBr :: c Tagged => Optic c s t a b -> (b -> t)
exBr b = exBrs b id

(<~) :: c Tagged => Optic c s t a b -> (b -> t)
(<~) = exBr

infixr 9 <~

(~>) :: c (Forget a) => s -> Optic c s t a b -> a
(~>) = flip exBl

infixl 9 ~>


over :: (c Tagged, c (Forget a)) => Optic c s t a b -> (t -> s) -> (b -> a)
over b = dimap (b <~) (~> b)

under :: (c Tagged, c (Forget a)) => Optic c s t a b -> (a -> b) -> (s -> t)
under b = dimap (~> b) (b <~)


-- Construction

(<->) :: (s -> a) -> (b -> t) -> Optic Iso s t a b
l <-> r = Optic (dimap l r)

from :: Optic Iso s t a b -> Optic Iso b a t s
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

bij :: (a -> b, b -> a) <-> (a <-> b)
bij = uncurry (<->) <-> ((,) <$> exBl <*> exBr)


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


-- Representable

tabulated :: Co.Representable f => (Co.Rep f -> a) <-> f a
tabulated = Co.tabulate <-> Co.index

contratabulated :: Contra.Representable f => (a -> Contra.Rep f) <-> f a
contratabulated = Contra.tabulate <-> Contra.index


-- Adjunction

adjuncted :: Co.Adjunction f u => (f a -> b) <-> (a -> u b)
adjuncted = Co.leftAdjunct <-> Co.rightAdjunct

contraadjuncted :: Contra.Adjunction f u => (a -> f b) <-> (b -> u a)
contraadjuncted = Contra.leftAdjunct <-> Contra.rightAdjunct


-- Functor

fmapping :: Functor f => (a <-> a') -> f a <-> f a'
fmapping a = fmap (exBl a) <-> fmap (exBr a)

contramapping :: Contravariant f => (a <-> a') -> f a <-> f a'
contramapping a = contramap (exBr a) <-> contramap (exBl a)


-- Bifunctor

bimapping :: Bifunctor p => (a <-> a') -> (b <-> b') -> (a `p` b) <-> (a' `p` b')
bimapping a b = bimap (exBl a) (exBl b) <-> bimap (exBr a) (exBr b)

firsting :: Bifunctor p => (a <-> a') -> (a `p` b) <-> (a' `p` b)
firsting a = first (exBl a) <-> first (exBr a)

seconding :: Bifunctor p => (b <-> b') -> (a `p` b) <-> (a `p` b')
seconding b = second (exBl b) <-> second (exBr b)


-- Profunctor

dimapping :: Profunctor p => (a <-> a') -> (b <-> b') -> (a `p` b) <-> (a' `p` b')
dimapping a b = dimap (exBr a) (exBl b) <-> dimap (exBl a) (exBr b)

lmapping :: Profunctor p => (a <-> a') -> (a `p` b) <-> (a' `p` b)
lmapping a = lmap (exBr a) <-> lmap (exBl a)

rmapping :: Profunctor p => (b <-> b') -> (a `p` b) <-> (a `p` b')
rmapping b = rmap (exBl b) <-> rmap (exBr b)


-- Tagged

newtype Tagged a b = Tagged { getTagged :: b }
  deriving (Functor)

instance Applicative (Tagged a) where
  pure = Tagged
  (<*>) = coerce

instance Profunctor Tagged where
  dimap _ g = Tagged . g . getTagged

instance Choice Tagged where
  left'  = Tagged . Left  . getTagged
  right' = Tagged . Right . getTagged

instance Closed Tagged where
  closed (Tagged b) = Tagged (const b)
