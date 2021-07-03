{-# LANGUAGE FunctionalDependencies #-}
module Focalized.Continuation
( -- * Continuations
  type (•)(..)
  -- ** Construction
, Contrapplicative(..)
  -- ** Elimination
, runK0
, runK1
, runK2
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


-- Construction

class Contravariant k => Contrapplicative r k | k -> r where
  liftK0 :: (a -> r) -> k a
  liftK1 :: ((a -> r) -> (b -> r)) -> (k a -> k b)
  liftK2 :: ((a -> r) -> (b -> r) -> (c -> r)) -> (k a -> k b -> k c)

instance Contrapplicative r ((•) r) where
  liftK0 = K

  liftK1 = dimap (•) K

  liftK2 f (K a) (K b) = K (f a b)


-- Elimination

runK0 :: r •a -> (a -> r)
runK0 = (•)

runK1 :: (r •a -> r •b) -> ((a -> r) -> (b -> r))
runK1 = dimap K (•)

runK2 :: (r •a -> r •b -> r •c) -> ((a -> r) -> (b -> r) -> (c -> r))
runK2 f a b = runK0 (f (K a) (K b))


-- Composition

idK :: r •r
idK = K id


(•<<) :: Contravariant k => k a -> (b -> a) -> k b
(•<<) = flip contramap

(>>•) :: Contravariant k => (b -> a) -> k a -> k b
(>>•) = contramap

infixr 1 •<<, >>•

(<<•) :: (r -> s) -> r •a -> s •a
f <<• k = K (f . runK0 k)

(•>>) :: r •a -> (r -> s) -> s •a
k •>> f = K (f . runK0 k)

infixr 1 <<•, •>>


(<••>) :: Disj d => c •a -> c •b -> c •(a `d` b)
(<••>) = liftK2 (<-->)

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
