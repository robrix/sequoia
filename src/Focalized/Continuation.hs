{-# LANGUAGE TypeFamilies #-}
module Focalized.Continuation
( -- * Continuations
  type (•)(..)
  -- ** Application
, appK1
, appK2
, Continuation(..)
, inK1
, inK2
, exK1
, exK2
  -- ** Coercion
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
, type (••)
, type (**)
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
, Cont(..)
) where

import qualified Control.Category as Cat
import           Control.Monad (ap)
import           Data.Functor.Contravariant
import           Data.Profunctor
import           Focalized.Disjunction

-- Continuations

newtype r •a = K { (•) :: a -> r }

infixl 9 •

instance Cat.Category (•) where
  id = idK
  (.) = composeK

instance Contravariant ((•) r) where
  contramap = contramapK


-- Application

appK1 :: Continuation k => (k b -> k a) -> (a -> k **b)
appK1 f a = inK (\ k -> exK (f k) a)

appK2 :: Continuation k => (k (k c -> k b) -> k a) -> (a -> b -> k **c)
appK2 f a b = inK (\ k -> exK1 f (\ f -> exK (f k) b) a)


class Contravariant k => Continuation k where
  type R k

  inK :: (a -> R k) -> k a
  exK :: k a        -> (a -> R k)

instance Continuation ((•) r) where
  type R ((•) r) = r

  inK = K
  exK = (•)


inK1 :: Continuation k => ((a -> R k) -> (b -> R k)) -> (k a -> k b)
inK1 = dimap exK inK

inK2 :: Continuation k => ((a -> R k) -> (b -> R k) -> (c -> R k)) -> (k a -> k b -> k c)
inK2 = dimap2 exK exK inK


exK1 :: Continuation k => (k a -> k b) -> ((a -> R k) -> (b -> R k))
exK1 = dimap inK exK

exK2 :: Continuation k => (k a -> k b -> k c) -> ((a -> R k) -> (b -> R k) -> (c -> R k))
exK2 = dimap2 inK inK exK


dimap2 :: (a' -> a) -> (b' -> b) -> (c -> c') -> (a -> b -> c) -> (a' -> b' -> c')
dimap2 l1 l2 r f a1 a2 = r (f (l1 a1) (l2 a2))


-- Coercion

coerceK :: (Continuation k1, Continuation k2, R k1 ~ R k2) => k1 a -> k2 a
coerceK = inK . exK

coerceK1 :: (Continuation k1, Continuation k2, R k1 ~ R k2) => (k1 a -> k1 b) -> (k2 a -> k2 b)
coerceK1 = inK1 . exK1

coerceK2 :: (Continuation k1, Continuation k2, R k1 ~ R k2) => (k1 a -> k1 b -> k1 c) -> (k2 a -> k2 b -> k2 c)
coerceK2 = inK2 . exK2


-- Contravariant

contramapK :: Continuation k => (a' -> a) -> (k a -> k a')
contramapK f = inK . lmap f . exK


-- Category

idK :: Continuation k => k (R k)
idK = inK id

composeK :: (Continuation j, Continuation k) => j a -> k (R j) -> k a
composeK = dimap2 exK exK inK (flip (.))


-- Composition

(•<<) :: Contravariant k => k a -> (b -> a) -> k b
(•<<) = flip contramap

(>>•) :: Contravariant k => (b -> a) -> k a -> k b
(>>•) = contramap

infixr 1 •<<, >>•

(<<•) :: (Continuation j, Continuation k) => (R j -> R k) -> (j a -> k a)
f <<• k = inK (f . exK k)

(•>>) :: (Continuation j, Continuation k) => j a -> (R j -> R k) -> k a
k •>> f = inK (f . exK k)

infixr 1 <<•, •>>


(<••>) :: (Disj d, Continuation k) => k a -> k b -> k (a `d` b)
(<••>) = inK2 (<-->)

infix 3 <••>


(>>-) :: Continuation k => a -> (b -> k a) -> k b
a >>- f = inK ((`exK` a) . f)

infixl 1 >>-

(-<<) :: Continuation k => (b -> k a) -> (a -> k b)
f -<< a = inK ((`exK` a) . f)

infixr 1 -<<


-- Double negation

type r ••a = r •(r •a)

type k **a = k (k a)

infixl 9 ••, **


-- Construction

liftDN :: Continuation k => a -> k **a
liftDN = inK . flip exK

liftDN0 :: Continuation k => ((a -> R k) -> R k) -> k **a
liftDN0 = inK . lmap exK

liftDN1 :: Continuation k => (((a -> R k) -> R k) -> ((b -> R k) -> R k)) -> (k **a -> k **b)
liftDN1 = dimap runDN0 liftDN0

liftDN2 :: Continuation k => (((a -> R k) -> R k) -> ((b -> R k) -> R k) -> ((c -> R k) -> R k)) -> (k **a -> k **b -> k **c)
liftDN2 = dimap2 runDN0 runDN0 liftDN0


-- Elimination

runDN0 :: Continuation k => k **a -> ((a -> R k) -> R k)
runDN0 = lmap inK . exK

runDN1 :: Continuation k => (k **a -> k **b) -> (((a -> R k) -> R k) -> ((b -> R k) -> R k))
runDN1 = dimap liftDN0 runDN0

runDN2 :: Continuation k => (k **a -> k **b -> k **c) -> (((a -> R k) -> R k) -> ((b -> R k) -> R k) -> ((c -> R k) -> R k))
runDN2 = dimap2 liftDN0 liftDN0 runDN0


-- Cont monad

newtype Cont k a = Cont { runCont :: k **a }

instance Contravariant k => Functor (Cont k) where
  fmap f = Cont . (•<< (•<< f)) . runCont

instance Continuation k => Applicative (Cont k) where
  pure = Cont . liftDN
  (<*>) = ap

instance Continuation k => Monad (Cont k) where
  Cont m >>= f = Cont (m •<< inK . \ k a -> exK (runCont (f a)) k)
