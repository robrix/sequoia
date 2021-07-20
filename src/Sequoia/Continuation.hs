{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Continuation
( -- * Continuations
  Continuation
, KRep
, KFn
, Contravariant(..)
, Representable(..)
  -- ** Construction
, inK
, inK1
, inK1'
, inK2
, negK
, negK2
  -- ** Elimination
, exK
, exK1
, exK2
, (•)
  -- ** Coercion
, _K
, coerceKWith
, coerceK
, coerceK1
, coerceK2
  -- ** Category
, idK
, composeK
  -- ** Composition
, (<<•)
, (•>>)
, (<••>)
, (<•••>)
, (>>-)
, (-<<)
  -- ** Computation
, mapKRep
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
  -- * Ambient control
, Res(..)
, cont
, (••)
, Res1(..)
, cont1
, Res2(..)
) where

import Control.Applicative (liftA2)
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Rep
import Data.Profunctor
import Sequoia.Disjunction
import Sequoia.Functor.K
import Sequoia.Optic.Getter
import Sequoia.Optic.Iso
import Sequoia.Optic.Review
import Sequoia.Optic.Setter

-- Continuations

class Representable k => Continuation k

type KRep k = Rep k
type KFn k a = a -> KRep k


instance Continuation (K r)


-- Construction

inK :: Representable k => KFn k a ->       k a
inK = tabulate

inK1 :: Representable k => (KFn k a -> KFn k b) -> (k a -> k b)
inK1 = over _K

inK1' :: Representable k => (a -> (b -> KRep k)) -> (a -> k b)
inK1' = fmap inK

inK2 :: Representable k => (KFn k a -> KFn k b -> KFn k c) -> (k a -> k b -> k c)
inK2 f a b = inK (exK a `f` exK b)


-- | Negate a unary function by translating it to operate on continuations.
negK :: Representable k => (a -> b) -> (k b -> k a)
negK = inK1 . flip (.)

-- | Negate a binary function by translating it to operate on continuations.
negK2 :: Representable k => (a -> b -> c) -> (k (k c -> k b) -> k a)
negK2 = negK . (negK .)


-- Elimination

exK :: Representable k =>       k a -> KFn k a
exK = index

exK1 :: Representable k => (k a -> k b) -> (KFn k a -> KFn k b)
exK1 = under _K

exK2 :: Representable k => (k a -> k b -> k c) -> (KFn k a -> KFn k b -> KFn k c)
exK2 f a b = exK (inK a `f` inK b)


(•) :: Representable k => k a -> KFn k a
(•) = index

infixl 7 •


-- Coercion

_K :: (Representable k, Representable k') => Iso (k a) (k' a') (KFn k a) (KFn k' a')
_K = exK <-> inK


coerceKWith :: (Representable k1, Representable k2) => (KFn k1 a -> KFn k2 b) -> (k1 a -> k2 b)
coerceKWith = over _K

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
composeK j k = inK (exK k . exK j)


-- Composition

(<<•) :: (Representable j, Representable k) => (KRep j -> KRep k) -> (j a -> k a)
f <<• k = inK (f . exK k)

(•>>) :: (Representable j, Representable k) => j a -> (KRep j -> KRep k) -> k a
k •>> f = inK (f . exK k)

infixr 1 <<•, •>>


(<••>) :: (Disj d, Representable k) => k a -> k b -> k (a `d` b)
(<••>) = inK2 (<-->)

infix 3 <••>


(<•••>) :: (Disj d, Representable k) => (e -> k a) -> (e -> k b) -> (e -> k (a `d` b))
(<•••>) = liftA2 (<••>)

infix 3 <•••>


(>>-) :: Representable k => a -> (b -> k a) -> k b
a >>- f = inK ((• a) . f)

infixl 1 >>-

(-<<) :: Representable k => (b -> k a) -> (a -> k b)
f -<< a = inK ((• a) . f)

infixr 1 -<<


-- Computation

mapKRep :: (Representable k, Representable k') => (KRep k -> KRep k') -> (k a -> k' a)
mapKRep f = inK . (f .) . exK


-- Double negation

type k **a = k (k a)

infixl 9 **


type ContFn k a = KFn k (KFn k a)


_DN :: (Representable k, Representable k') => Iso (ContFn k a) (ContFn k' a') (k **a) (k' **a')
_DN = inDN <-> exDN


mapDN :: Representable k => (a -> b) -> (k **a -> k **b)
mapDN f = inK1 (lmap (contramap f))

hoistDN :: Representable j => (forall x . j x <-> k x) -> (j **a -> k **a)
hoistDN b = (^. b) . contramap (review b)


-- Construction

liftDN :: Representable k => a -> k **a
liftDN = inK . flip exK

inDN :: Representable k => ContFn k a -> k **a
inDN = inK . lmap exK

inDN1 :: Representable k => (ContFn k a -> ContFn k b) -> (k **a -> k **b)
inDN1 = dimap exDN inDN

inDN2 :: Representable k => (ContFn k a -> ContFn k b -> ContFn k c) -> (k **a -> k **b -> k **c)
inDN2 f a b = inDN (exDN a `f` exDN b)


-- Elimination

exDN :: Representable k => k **a -> ContFn k a
exDN = lmap inK . exK

exDN1 :: Representable k => (k **a -> k **b) -> (ContFn k a -> ContFn k b)
exDN1 = dimap inDN exDN

exDN2 :: Representable k => (k **a -> k **b -> k **c) -> (ContFn k a -> ContFn k b -> ContFn k c)
exDN2 f a b = exDN (inDN a `f` inDN b)


-- Ambient control

class Res c where
  res :: r -> c e r
  liftRes :: ((c e r -> r) -> c e r) -> c e r

instance Res (->) where
  res = pure
  liftRes f = f =<< flip ($)

cont :: (Res c, Representable k) => (((a -> c e (Rep k)) -> k a) -> c e (Rep k)) -> c e (Rep k)
cont = liftRes . contN

(••) :: (Res c, Representable k) => k a -> a -> c e (Rep k)
k •• v = res (k • v)

infix 7 ••


class Res1 c where
  res1 :: r -> c e r a
  liftRes1 :: ((c e r a -> r) -> c e r a) -> c e r a

cont1 :: (Res1 c, Representable k) => (((a -> c e (Rep k) a) -> k a) -> c e (Rep k) a) -> c e (Rep k) a
cont1 = liftRes1 . contN


class Res2 c where
  res2 :: r -> c e r a b
  liftRes2 :: ((c e r a b -> r) -> c e r a b) -> c e r a b


contN :: Representable k => (((a -> c) -> k a) -> c) -> ((c -> Rep k) -> c)
contN f run = f (inK . (run .))
