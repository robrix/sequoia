module Sequoia.Bijection
( -- * Bijections
  type (<->)(..)
  -- ** Elimination
, exBl
, exBr
, (<~)
, (~>)
  -- ** Construction
, (<->)
, inv
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
) where

import           Control.Applicative (Alternative)
import qualified Control.Category as Cat
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

newtype a <-> b = Bij { runBij :: forall r . ((a -> b) -> (b -> a) -> r) -> r }

infix 1 <->

instance Cat.Category (<->) where
  id = id <-> id
  f . g = (exBl f . exBl g) <-> (exBr g . exBr f)


-- Elimination

exBl :: a <-> b -> (a -> b)
exBl b = runBij b const

exBr :: a <-> b -> (b -> a)
exBr b = runBij b (const id)

(<~) :: a <-> b -> (b -> a)
(<~) = exBr

infixr 9 <~

(~>) :: a -> a <-> b -> b
b ~> x = exBl x b

infixl 9 ~>


-- Construction

(<->) :: (a -> b) -> (b -> a) -> a <-> b
l <-> r = Bij (\ f -> f l r)

inv :: a <-> b -> b <-> a
inv b = (b <~) <-> (~> b)

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
bij = uncurry (<->) <-> flip runBij (,)


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
