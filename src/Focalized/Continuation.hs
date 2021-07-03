{-# LANGUAGE TypeFamilies #-}
module Focalized.Continuation
( -- * Continuations
  type (•)(..)
  -- ** Application
, appK1
, appK2
, Contrapplicative(..)
, coerceK
, coerceK1
, coerceK2
  -- ** Composition
, idK
, (•<<)
, (>>•)
, (<<•)
, (•>>)
, (<••>)
, (>>-)
, (-<<)
  -- * Double negation
, type (••)
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
  K f . K g = K (g . f)

instance Contravariant ((•) r) where
  contramap f = K . lmap f . (•)


-- Application

appK1 :: Contrapplicative k => (k b -> k a) -> (a -> k (k b))
appK1 f a = inK (\ k -> exK (f k) a)

appK2 :: Contrapplicative k => (k (k c -> k b) -> k a) -> (a -> b -> k (k c))
appK2 f a b = inK (\ k -> exK1 f (\ f -> exK (f k) b) a)


class Contravariant k => Contrapplicative k where
  type R k

  inK :: (a -> R k) -> k a
  inK1 :: ((a -> R k) -> (b -> R k)) -> (k a -> k b)
  inK2 :: ((a -> R k) -> (b -> R k) -> (c -> R k)) -> (k a -> k b -> k c)

  exK :: k a -> (a -> R k)
  exK1 :: (k a -> k b) -> ((a -> R k) -> (b -> R k))
  exK2 :: (k a -> k b -> k c) -> ((a -> R k) -> (b -> R k) -> (c -> R k))

instance Contrapplicative ((•) r) where
  type R ((•) r) = r

  inK = K

  inK1 = dimap (•) K

  inK2 f (K a) (K b) = K (f a b)

  exK = (•)

  exK1 = dimap K (•)

  exK2 f a b = exK (f (K a) (K b))


coerceK :: (Contrapplicative k1, Contrapplicative k2, R k1 ~ R k2) => k1 a -> k2 a
coerceK = inK . exK

coerceK1 :: (Contrapplicative k1, Contrapplicative k2, R k1 ~ R k2) => (k1 a -> k1 b) -> (k2 a -> k2 b)
coerceK1 = inK1 . exK1

coerceK2 :: (Contrapplicative k1, Contrapplicative k2, R k1 ~ R k2) => (k1 a -> k1 b -> k1 c) -> (k2 a -> k2 b -> k2 c)
coerceK2 = inK2 . exK2


-- Composition

idK :: r •r
idK = K id


(•<<) :: Contravariant k => k a -> (b -> a) -> k b
(•<<) = flip contramap

(>>•) :: Contravariant k => (b -> a) -> k a -> k b
(>>•) = contramap

infixr 1 •<<, >>•

(<<•) :: (r -> s) -> r •a -> s •a
f <<• k = K (f . exK k)

(•>>) :: r •a -> (r -> s) -> s •a
k •>> f = K (f . exK k)

infixr 1 <<•, •>>


(<••>) :: (Disj d, Contrapplicative k) => k a -> k b -> k (a `d` b)
(<••>) = inK2 (<-->)

infix 3 <••>


(>>-) :: a -> (b -> r •a) -> r •b
a >>- f = K ((• a) . f)

infixl 1 >>-

(-<<) :: (b -> r •a) -> (a -> r •b)
f -<< a = K ((• a) . f)

infixr 1 -<<


-- Double negation

type r ••a = r •(r •a)

infixl 9 ••


-- Construction

liftDN :: a -> r ••a
liftDN = K . flip (•)

liftDN0 :: ((a -> r) -> r) -> r ••a
liftDN0 = K . lmap (•)

liftDN1 :: (((a -> r) -> r) -> ((b -> r) -> r)) -> (r ••a -> r ••b)
liftDN1 = dimap runDN0 liftDN0

liftDN2 :: (((a -> r) -> r) -> ((b -> r) -> r) -> ((c -> r) -> r)) -> (r ••a -> r ••b -> r ••c)
liftDN2 f a b = liftDN0 (f (runDN0 a) (runDN0 b))


-- Elimination

runDN0 :: r ••a -> ((a -> r) -> r)
runDN0 = lmap K . (•)

runDN1 :: (r ••a -> r ••b) -> (((a -> r) -> r) -> ((b -> r) -> r))
runDN1 = dimap liftDN0 runDN0

runDN2 :: (r ••a -> r ••b -> r ••c) -> (((a -> r) -> r) -> ((b -> r) -> r) -> ((c -> r) -> r))
runDN2 f a b = runDN0 (f (liftDN0 a) (liftDN0 b))


-- Cont monad

newtype Cont r a = Cont { runCont :: r ••a }

instance Functor (Cont r) where
  fmap f = Cont . (•<< (•<< f)) . runCont

instance Applicative (Cont r) where
  pure = Cont . K . flip (•)
  (<*>) = ap

instance Monad (Cont r) where
  Cont m >>= f = Cont (m •<< K . \ k a -> runCont (f a) • k)
