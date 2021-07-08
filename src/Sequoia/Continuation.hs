{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Continuation
( -- * Continuations
  Continuation
, KRep
  -- ** Application
, KFn
, _K
, inK
, inK1
, inK2
, exK
, exK1
, exK2
, (•)
  -- ** Coercion
, coerceKWith
, coerceK
, coerceK1
, coerceK2
  -- ** Category
, idK
, composeK
  -- ** Composition
, (•<<)
, (>>•)
, (<<•)
, (•>>)
, (<••>)
, (>>-)
, (-<<)
  -- * Double negation
, type (**)
, ContFn
, _DN
, mapDN
, hoistDN
  -- ** Construction
, liftDN
, inDN
, inDN1
, inDN2
  -- ** Elimination
, exDN
, exDN1
, exDN2
  -- * Cont monad
, Cont(..)
, inCont
, exCont
  -- * Monadic abstraction
, MonadK(..)
) where

import Control.Monad (ap)
import Data.Profunctor
import Data.Profunctor.Rep
import Data.Profunctor.Sieve
import Sequoia.Bijection
import Sequoia.Disjunction
import Sequoia.Profunctor.K

-- Continuations

class Representable k => Continuation k

type KRep k = Rep k


instance Continuation (K r)


-- Application

type KFn k r a = a -> KRep k r

_K :: (Representable k, Representable k') => Optic Iso (k a r) (k' a' r') (KFn k r a) (KFn k' r' a')
_K = exK <-> inK


inK :: Representable k => KFn k r a ->       k a r
inK = tabulate

inK1 :: Representable k => (KFn k r a -> KFn k r b) -> (k a r -> k b r)
inK1 = under _K

inK2 :: Representable k => (KFn k r a -> KFn k r b -> KFn k r c) -> (k a r -> k b r -> k c r)
inK2 = dimap2 exK exK inK


exK :: Representable k =>       k a r -> KFn k r a
exK = sieve

exK1 :: Representable k => (k a r -> k b r) -> (KFn k r a -> KFn k r b)
exK1 = over _K

exK2 :: Representable k => (k a r -> k b r -> k c r) -> (KFn k r a -> KFn k r b -> KFn k r c)
exK2 = dimap2 inK inK exK


(•) :: Representable k => k a r -> KFn k r a
(•) = sieve

infixl 9 •


-- Coercion

coerceKWith :: (Representable k1, Representable k2) => (KFn k1 r a -> KFn k2 r b) -> (k1 a r -> k2 b r)
coerceKWith = under _K

coerceK :: (Representable k1, Representable k2, Rep k1 ~ Rep k2) => (k1 a r -> k2 a r)
coerceK = inK . exK

coerceK1 :: (Representable k1, Representable k2, Rep k1 ~ Rep k2) => (k1 a r -> k1 b r) -> (k2 a r -> k2 b r)
coerceK1 = inK1 . exK1

coerceK2 :: (Representable k1, Representable k2, Rep k1 ~ Rep k2) => (k1 a r -> k1 b r -> k1 c r) -> (k2 a r -> k2 b r -> k2 c r)
coerceK2 = inK2 . exK2


-- Category

idK :: Representable k => k (KRep k r) r
idK = inK id

composeK :: (Representable j, Representable k) => j a r -> k (KRep j r) r -> k a r
composeK = dimap2 exK exK inK (flip (.))


-- Composition

(•<<) :: Profunctor k => k a r -> (b -> a) -> k b r
(•<<) = flip lmap

(>>•) :: Profunctor k => (b -> a) -> k a r -> k b r
(>>•) = lmap

infixr 1 •<<, >>•

(<<•) :: (Representable j, Representable k) => (KRep j r -> KRep k r) -> (j a r -> k a r)
f <<• k = inK (f . exK k)

(•>>) :: (Representable j, Representable k) => j a r -> (KRep j r -> KRep k r) -> k a r
k •>> f = inK (f . exK k)

infixr 1 <<•, •>>


(<••>) :: (Disj d, Representable k) => k a r -> k b r -> k (a `d` b) r
(<••>) = inK2 (<-->)

infix 3 <••>


(>>-) :: Representable k => a -> (b -> k a r) -> k b r
a >>- f = inK ((• a) . f)

infixl 1 >>-

(-<<) :: Representable k => (b -> k a r) -> (a -> k b r)
f -<< a = inK ((• a) . f)

infixr 1 -<<


-- Double negation

type k **a = k (k a ()) ()

infixl 9 **


type ContFn k a = KFn k () (KFn k () a)


_DN :: (Representable k, Representable k') => Optic Iso (ContFn k a) (ContFn k' a') (k **a) (k' **a')
_DN = inDN <-> exDN


mapDN :: Continuation k => (a -> b) -> (k **a -> k **b)
mapDN f = inK1 (lmap (lmap f))

hoistDN :: Profunctor j => (forall x . j x () <-> k x ()) -> (j **a -> k **a)
hoistDN b = (~> b) . lmap (b <~)


-- Construction

liftDN :: Representable k => a -> k **a
liftDN = inK . flip exK

inDN :: Representable k => ContFn k a -> k **a
inDN = inK . lmap exK

inDN1 :: Representable k => (ContFn k a -> ContFn k b) -> (k **a -> k **b)
inDN1 = dimap exDN inDN

inDN2 :: Representable k => (ContFn k a -> ContFn k b -> ContFn k c) -> (k **a -> k **b -> k **c)
inDN2 = dimap2 exDN exDN inDN


-- Elimination

exDN :: Representable k => k **a -> ContFn k a
exDN = lmap inK . exK

exDN1 :: Representable k => (k **a -> k **b) -> (ContFn k a -> ContFn k b)
exDN1 = dimap inDN exDN

exDN2 :: Representable k => (k **a -> k **b -> k **c) -> (ContFn k a -> ContFn k b -> ContFn k c)
exDN2 = dimap2 inDN inDN exDN


-- Cont monad

newtype Cont k a = Cont { runCont :: k **a }

instance Profunctor k => Functor (Cont k) where
  fmap f = Cont . (•<< (•<< f)) . runCont

instance Representable k => Applicative (Cont k) where
  pure = Cont . liftDN
  (<*>) = ap

instance Representable k => Monad (Cont k) where
  Cont m >>= f = Cont (m •<< inK . \ k a -> runCont (f a) • k)


inCont :: Representable k => ContFn k a -> Cont k a
inCont = Cont . inK . lmap exK

exCont :: Representable k => Cont k a -> ContFn k a
exCont = lmap inK . exK . runCont


-- Monadic abstraction

class (Profunctor k, Monad m) => MonadK k m | m -> k where
  jump :: k **a -> m a

instance Representable k => MonadK k (Cont k) where
  jump = Cont
