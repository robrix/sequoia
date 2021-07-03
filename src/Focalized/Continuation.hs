{-# LANGUAGE TypeFamilies #-}
module Focalized.Continuation
( -- * Continuations
  K(..)
  -- ** Application
, appK1
, appK2
, Representable(..)
, inK
, inK1
, inK2
, exK
, exK1
, exK2
, dimap2
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
, type (**)
, ContFn
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
import           Data.Functor.Contravariant.Rep
import           Data.Profunctor
import           Focalized.Disjunction

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


-- Application

appK1 :: Representable k => (k b -> k a) -> (a -> k **b)
appK1 f a = inK (\ k -> exK (f k) a)

appK2 :: Representable k => (k (k c -> k b) -> k a) -> (a -> b -> k **c)
appK2 f a b = inK (\ k -> exK1 f (\ f -> exK (f k) b) a)


inK :: Representable k => (a -> Rep k) -> k a
inK = tabulate

exK :: Representable k => k a          -> (a -> Rep k)
exK = index


inK1 :: Representable k => ((a -> Rep k) -> (b -> Rep k)) -> (k a -> k b)
inK1 = dimap exK inK

inK2 :: Representable k => ((a -> Rep k) -> (b -> Rep k) -> (c -> Rep k)) -> (k a -> k b -> k c)
inK2 = dimap2 exK exK inK


exK1 :: Representable k => (k a -> k b) -> ((a -> Rep k) -> (b -> Rep k))
exK1 = dimap inK exK

exK2 :: Representable k => (k a -> k b -> k c) -> ((a -> Rep k) -> (b -> Rep k) -> (c -> Rep k))
exK2 = dimap2 inK inK exK


dimap2 :: (a' -> a) -> (b' -> b) -> (c -> c') -> (a -> b -> c) -> (a' -> b' -> c')
dimap2 l1 l2 r f a1 a2 = r (f (l1 a1) (l2 a2))


-- Coercion

coerceK :: (Representable k1, Representable k2, Rep k1 ~ Rep k2) => k1 a -> k2 a
coerceK = inK . exK

coerceK1 :: (Representable k1, Representable k2, Rep k1 ~ Rep k2) => (k1 a -> k1 b) -> (k2 a -> k2 b)
coerceK1 = inK1 . exK1

coerceK2 :: (Representable k1, Representable k2, Rep k1 ~ Rep k2) => (k1 a -> k1 b -> k1 c) -> (k2 a -> k2 b -> k2 c)
coerceK2 = inK2 . exK2


-- Contravariant

contramapK :: Representable k => (a' -> a) -> (k a -> k a')
contramapK f = inK . lmap f . exK


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
a >>- f = inK ((`exK` a) . f)

infixl 1 >>-

(-<<) :: Representable k => (b -> k a) -> (a -> k b)
f -<< a = inK ((`exK` a) . f)

infixr 1 -<<


-- Double negation

type k **a = k (k a)

infixl 9 **


type ContFn k a = (a -> Rep k) -> Rep k


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
  Cont m >>= f = Cont (m •<< inK . \ k a -> exK (runCont (f a)) k)


inCont :: Representable k => ContFn k a -> k ••a
inCont = Cont . inK . lmap exK

exCont :: Representable k => k ••a -> ContFn k a
exCont = lmap inK . exK . runCont
