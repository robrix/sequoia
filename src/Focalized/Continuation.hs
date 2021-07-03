module Focalized.Continuation
( -- * Continuations
  type (•)(..)
  -- ** Construction
, liftK0
, liftK1
, liftK2
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
, liftDN0
, liftDN1
  -- ** Elimination
, runDN
) where

import qualified Control.Category as Cat
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

liftK0 :: (a -> r) -> r •a
liftK0 = K

liftK1 :: ((a -> r) -> (b -> r)) -> (r •a -> r •b)
liftK1 = dimap (•) K

liftK2 :: ((a -> r) -> (b -> r) -> (c -> r)) -> (r •a -> r •b -> r •c)
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


(•<<) :: r •a -> (b -> a) -> r •b
(•<<) = flip contramap

(>>•) :: (b -> a) -> r •a -> r •b
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

liftDN0 :: a -> r ••a
liftDN0 = K . flip (•)

liftDN1 :: ((a -> r) -> r) -> r ••a
liftDN1 = K . lmap (•)


-- Elimination

runDN :: r ••a -> ((a -> r) -> r)
runDN = lmap K . (•)
