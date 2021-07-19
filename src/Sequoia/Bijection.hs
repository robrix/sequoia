module Sequoia.Bijection
( -- * Bijections
  type (<->)
, Optic
  -- ** Elimination
, views
, reviews
, (<~)
, (~>)
, under
, over
  -- ** Construction
, from
, constant
, involuted
, flipped
, curried
, uncurried
, swapped
, non
-- , bij
, dimap2
  -- ** Composition
, idB
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
  -- * Isos
, Iso
, (<->)
  -- * Lenses
, Lens
, lens
, _fst
, _snd
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
import           Sequoia.Profunctor.Coexponential
import           Sequoia.Profunctor.Recall

-- Bijections

type a <-> b = Iso a a b b

infix 1 <->


type Optic p s t a b = (a `p` b) -> (s `p` t)


-- Elimination

views   :: Optic (Forget r) s t a b -> (a -> r) -> (s -> r)
views   b = runForget . b . Forget

reviews :: Optic (Recall e) s t a b -> (e -> b) -> (e -> t)
reviews b = runRecall . b . Recall


(~>) :: s -> Optic (Forget a) s t a b -> a
s ~> o = views o id s

infixl 8 ~>

(<~) :: Optic (Recall b) s t a b -> (b -> t)
o <~ b = reviews o id b

infixr 8 <~


under :: Optic (Coexp b a) s t a b -> (t -> s) -> (b -> a)
under = runCoexp . ($ idCoexp)

over :: Optic (->) s t a b -> (a -> b) -> (s -> t)
over f = f


-- Construction

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

-- bij :: (a <-> b) <-> (a -> b, b -> a)
-- bij = ((,) <$> flip (~>) <*> (<~)) <-> uncurry (<->)

dimap2 :: (a' -> a) -> (b' -> b) -> (c -> c') -> (a -> b -> c) -> (a' -> b' -> c')
dimap2 l1 l2 r f a1 a2 = r (f (l1 a1) (l2 a2))


-- Composition

idB :: Optic p s s s s
idB = id


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


-- Isos

type Iso s t a b = forall p . Profunctor p => Optic p s t a b

(<->) :: (s -> a) -> (b -> t) -> Iso s t a b
l <-> r = dimap l r


-- Lenses

type Lens s t a b = forall p . Strong p => Optic p s t a b

lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens prj inj = dimap (\ s -> (prj s, s)) (\ (b, s) -> inj s b) . first'


_fst :: Lens (a, b) (a', b) a a'
_fst = lens fst (\ ~(_, b) a' -> (a', b))

_snd :: Lens (a, b) (a, b') b b'
_snd = lens snd (\ ~(a, _) b' -> (a, b'))
