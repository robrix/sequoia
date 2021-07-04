{-# LANGUAGE TypeFamilies #-}
module Sequoia.Continuation
( -- * Continuations
  K(..)
  -- ** Application
, appK1
, appK2
, Representable(..)
, RepFn
, inK
, inK1
, inK2
, exK
, exK1
, exK2
, (•)
, dimap2
  -- ** Coercion
, coerceKWith
, coerceK
, coerceK1
, coerceK2
  -- ** Contravariant
, Contravariant(..)
, contramapK
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
, mapDN
  -- ** Construction
, liftDN
, liftDN0
, liftDN1
, liftDN2
  -- ** Elimination
, runDN0
, runDN1
, runDN2
  -- * Cont monad
, type (••)(..)
, inCont
, exCont
) where

import qualified Control.Category as Cat
import           Control.Monad (ap, (<=<))
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Adjunction
import           Data.Functor.Contravariant.Rep
import           Data.Profunctor
import           Sequoia.Bijection
import           Sequoia.Disjunction

-- Continuations

newtype K m r a = K { runK :: a -> m r }

instance Monad m => Cat.Category (K m) where
  id = K pure
  K f . K g = K (g <=< f)

instance Contravariant (K m r) where
  contramap = contramapK

instance Representable (K m r) where
  type Rep (K m r) = m r

  tabulate = K
  index = runK

instance Adjunction (K m r) (K m r) where
  unit   = inK . flip exK
  counit = inK . flip exK
  leftAdjunct  = (-<<)
  rightAdjunct = (-<<)


-- Application

appK1 :: Representable k => (k b -> k a) -> (a -> k **b)
appK1 = (-<<)

appK2 :: Representable k => (k (k c -> k b) -> k a) -> (a -> b -> k **c)
appK2 f a b = inK (\ k -> exK1 f (\ f -> f k • b) a)


type RepFn k a = a -> Rep k


inK :: Representable k => RepFn k a ->       k a
inK = tabulate

inK1 :: Representable k => (RepFn k a -> RepFn k b) -> (k a -> k b)
inK1 = dimap exK inK

inK2 :: Representable k => (RepFn k a -> RepFn k b -> RepFn k c) -> (k a -> k b -> k c)
inK2 = dimap2 exK exK inK


exK :: Representable k =>       k a -> RepFn k a
exK = index

exK1 :: Representable k => (k a -> k b) -> (RepFn k a -> RepFn k b)
exK1 = dimap inK exK

exK2 :: Representable k => (k a -> k b -> k c) -> (RepFn k a -> RepFn k b -> RepFn k c)
exK2 = dimap2 inK inK exK


(•) :: Representable k => k a -> RepFn k a
(•) = index


dimap2 :: (a' -> a) -> (b' -> b) -> (c -> c') -> (a -> b -> c) -> (a' -> b' -> c')
dimap2 l1 l2 r f a1 a2 = r (f (l1 a1) (l2 a2))


-- Coercion

coerceKWith :: (Representable k1, Representable k2) => (RepFn k1 a -> RepFn k2 b) -> (k1 a -> k2 b)
coerceKWith f = inK . f . exK

coerceK :: (Representable k1, Representable k2, Rep k1 ~ Rep k2) => (k1 a -> k2 a)
coerceK = inK . exK

coerceK1 :: (Representable k1, Representable k2, Rep k1 ~ Rep k2) => (k1 a -> k1 b) -> (k2 a -> k2 b)
coerceK1 = inK1 . exK1

coerceK2 :: (Representable k1, Representable k2, Rep k1 ~ Rep k2) => (k1 a -> k1 b -> k1 c) -> (k2 a -> k2 b -> k2 c)
coerceK2 = inK2 . exK2


-- Contravariant

contramapK :: Representable k => (a' -> a) -> (k a -> k a')
contramapK = inK1 . lmap


-- Category

idK :: Representable k => k (Rep k)
idK = inK id

composeK :: (Representable j, Representable k) => j a -> k (Rep j) -> k a
composeK = dimap2 exK exK inK (flip (.))


-- Composition

(•<<) :: Contravariant k => k a -> (b -> a) -> k b
(•<<) = flip contramap

(>>•) :: Contravariant k => (b -> a) -> k a -> k b
(>>•) = contramap

infixr 1 •<<, >>•

(<<•) :: (Representable j, Representable k) => (Rep j -> Rep k) -> (j a -> k a)
f <<• k = inK (f . exK k)

(•>>) :: (Representable j, Representable k) => j a -> (Rep j -> Rep k) -> k a
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


type ContFn k a = RepFn k (RepFn k a)


mapDN :: Contravariant j => (forall x . j x <-> k x) -> (j **a -> k **a)
mapDN b = (~> b) . contramap (b <~)


-- Construction

liftDN :: Representable k => a -> k **a
liftDN = inK . flip exK

liftDN0 :: Representable k => ContFn k a -> k **a
liftDN0 = inK . lmap exK

liftDN1 :: Representable k => (ContFn k a -> ContFn k b) -> (k **a -> k **b)
liftDN1 = dimap runDN0 liftDN0

liftDN2 :: Representable k => (ContFn k a -> ContFn k b -> ContFn k c) -> (k **a -> k **b -> k **c)
liftDN2 = dimap2 runDN0 runDN0 liftDN0


-- Elimination

runDN0 :: Representable k => k **a -> ContFn k a
runDN0 = lmap inK . exK

runDN1 :: Representable k => (k **a -> k **b) -> (ContFn k a -> ContFn k b)
runDN1 = dimap liftDN0 runDN0

runDN2 :: Representable k => (k **a -> k **b -> k **c) -> (ContFn k a -> ContFn k b -> ContFn k c)
runDN2 = dimap2 liftDN0 liftDN0 runDN0


-- Cont monad

newtype k ••a = Cont { runCont :: k **a }

infixr 9 ••

instance Contravariant k => Functor ((••) k) where
  fmap f = Cont . (•<< (•<< f)) . runCont

instance Representable k => Applicative ((••) k) where
  pure = Cont . liftDN
  (<*>) = ap

instance Representable k => Monad ((••) k) where
  Cont m >>= f = Cont (m •<< inK . \ k a -> runCont (f a) • k)


inCont :: Representable k => ContFn k a -> k ••a
inCont = Cont . inK . lmap exK

exCont :: Representable k => k ••a -> ContFn k a
exCont = lmap inK . exK . runCont
