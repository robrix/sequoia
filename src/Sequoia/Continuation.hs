{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Continuation
( -- * Continuations
  Continuation
, KRep
, Contravariant(..)
, Representable(..)
  -- ** Application
, KFn
, _K
, inK
, inK1
, inK1'
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
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Rep
import Data.Profunctor
import Sequoia.Bijection
import Sequoia.Disjunction
import Sequoia.Functor.K

-- Continuations

class Representable k => Continuation k

type KRep k = Rep k


instance Continuation (K r)


-- Application

type KFn k a = a -> KRep k

_K :: (Representable k, Representable k') => Optic Iso (k a) (k' a') (KFn k a) (KFn k' a')
_K = exK <-> inK


inK :: Representable k => KFn k a ->       k a
inK = tabulate

inK1 :: Representable k => (KFn k a -> KFn k b) -> (k a -> k b)
inK1 = under _K

inK1' :: Representable k => (a -> (b -> KRep k)) -> (a -> k b)
inK1' = fmap inK

inK2 :: Representable k => (KFn k a -> KFn k b -> KFn k c) -> (k a -> k b -> k c)
inK2 = dimap2 exK exK inK


exK :: Representable k =>       k a -> KFn k a
exK = index

exK1 :: Representable k => (k a -> k b) -> (KFn k a -> KFn k b)
exK1 = over _K

exK2 :: Representable k => (k a -> k b -> k c) -> (KFn k a -> KFn k b -> KFn k c)
exK2 = dimap2 inK inK exK


(•) :: Representable k => k a -> KFn k a
(•) = index

infixl 9 •


-- Coercion

coerceKWith :: (Representable k1, Representable k2) => (KFn k1 a -> KFn k2 b) -> (k1 a -> k2 b)
coerceKWith = under _K

coerceK :: (Representable k1, Representable k2, Rep k1 ~ Rep k2) => (k1 a -> k2 a)
coerceK = inK . exK

coerceK1 :: (Representable k1, Representable k2, Rep k1 ~ Rep k2) => (k1 a -> k1 b) -> (k2 a -> k2 b)
coerceK1 = inK1 . exK1

coerceK2 :: (Representable k1, Representable k2, Rep k1 ~ Rep k2) => (k1 a -> k1 b -> k1 c) -> (k2 a -> k2 b -> k2 c)
coerceK2 = inK2 . exK2


-- Category

idK :: Representable k => k (KRep k)
idK = inK id

composeK :: (Representable j, Representable k) => j a -> k (KRep j) -> k a
composeK = dimap2 exK exK inK (flip (.))


-- Composition

(•<<) :: Contravariant k => k a -> (b -> a) -> k b
(•<<) = flip contramap

(>>•) :: Contravariant k => (b -> a) -> k a -> k b
(>>•) = contramap

infixr 1 •<<, >>•

(<<•) :: (Representable j, Representable k) => (KRep j -> KRep k) -> (j a -> k a)
f <<• k = inK (f . exK k)

(•>>) :: (Representable j, Representable k) => j a -> (KRep j -> KRep k) -> k a
k •>> f = inK (f . exK k)

infixr 1 <<•, •>>


(<••>) :: (Disj d, Representable k) => k a -> k b -> k (a `d` b)
(<••>) = inK2 (<-->)

infix 3 <••>


(>>-) :: Representable k => a -> (b -> k a) -> k b
a >>- f = inK ((• a) . f)

infixl 1 >>-

(-<<) :: Representable k => (b -> k a) -> (a -> k b)
f -<< a = inK ((• a) . f)

infixr 1 -<<


-- Double negation

type k **a = k (k a)

infixl 9 **


type ContFn k a = KFn k (KFn k a)


_DN :: (Representable k, Representable k') => Optic Iso (ContFn k a) (ContFn k' a') (k **a) (k' **a')
_DN = inDN <-> exDN


mapDN :: Continuation k => (a -> b) -> (k **a -> k **b)
mapDN f = inK1 (lmap (contramap f))

hoistDN :: Continuation j => (forall x . j x <-> k x) -> (j **a -> k **a)
hoistDN b = (~> b) . contramap (b <~)


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

instance Contravariant k => Functor (Cont k) where
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

class (Contravariant k, Monad m) => MonadK k m | m -> k where
  jump :: k **a -> m a

instance Representable k => MonadK k (Cont k) where
  jump = Cont
