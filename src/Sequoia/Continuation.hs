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
, negK2
  -- ** Elimination
, (•)
  -- ** Coercion
, _K
  -- ** Category
, idK
  -- ** Composition
, (<••>)
, (<•••>)
  -- * Double negation
, type (**)
, mapDN
  -- ** Construction
, liftDN
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
import Sequoia.Optic.Iso
import Sequoia.Optic.Setter
import Sequoia.Profunctor.Recall

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
inK2 f a b = inK ((a •) `f` (b •))


-- | Negate a binary function by translating it to operate on continuations.
negK2 :: Contravariant k => (a -> b -> c) -> (k (k c -> k b) -> k a)
negK2 = contramap . (contramap .)


-- Elimination

(•) :: Representable k => k a -> KFn k a
(•) = index

infixl 7 •


-- Coercion

_K :: (Representable k, Representable k') => Iso (k a) (k' a') (KFn k a) (KFn k' a')
_K = from contratabulated


-- Category

idK :: Representable k => k (KRep k)
idK = inK id


-- Composition

(<••>) :: (Disj d, Representable k) => k a -> k b -> k (a `d` b)
(<••>) = inK2 (<-->)

infix 3 <••>


(<•••>) :: (Disj d, Representable k) => (e -> k a) -> (e -> k b) -> (e -> k (a `d` b))
(<•••>) = liftA2 (<••>)

infix 3 <•••>


-- Double negation

type k **a = k (k a)

infixl 9 **


type ContFn k a = KFn k (KFn k a)


_DN :: (Representable k, Representable k') => Iso (ContFn k a) (ContFn k' a') (k **a) (k' **a')
_DN = inDN <-> exDN


mapDN :: Representable k => (a -> b) -> (k **a -> k **b)
mapDN f = inK1 (lmap (contramap f))


-- Construction

liftDN :: Representable k => a -> k **a
liftDN = inK . flip (•)

inDN :: Representable k => ContFn k a -> k **a
inDN = inK . lmap (•)


-- Elimination

exDN :: Representable k => k **a -> ContFn k a
exDN = lmap inK . (•)


-- Ambient control

class Res c where
  res :: r -> c e r
  liftRes :: ((c e r -> r) -> c e r) -> c e r

instance Res (->) where
  res = pure
  liftRes f = f =<< flip ($)

instance Res (Recall e) where
  res = Recall . pure
  liftRes f = Recall (\ e -> runRecall (f (`runRecall` e)) e)

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
