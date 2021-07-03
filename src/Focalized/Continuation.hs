module Focalized.Continuation
( -- * Continuations
  type (•)(..)
  -- ** Construction
, liftK1
, liftK2
  -- ** Elimination
, runK
, lowerK1
, lowerK2
  -- ** Composition
, idK
, (•<<)
, (>>•)
, (<<•)
, (•>>)
) where

import qualified Control.Category as Cat
import           Data.Functor.Contravariant
import           Data.Profunctor

-- Continuations

newtype r •a = K { (•) :: a -> r }

infixl 9 •

instance Cat.Category (•) where
  id = K id
  K f . K g = K (g . f)

instance Contravariant ((•) r) where
  contramap f = K . (. f) . (•)


-- Construction

liftK1 :: ((a -> r) -> (b -> r)) -> (r •a -> r •b)
liftK1 = dimap (•) K

liftK2 :: ((a -> r) -> (b -> r) -> (c -> r)) -> (r •a -> r •b -> r •c)
liftK2 f (K a) (K b) = K (f a b)


-- Elimination

runK :: r •a -> a -> r
runK = (•)

lowerK1 :: (r •a -> r •b) -> ((a -> r) -> (b -> r))
lowerK1 = dimap K (•)

lowerK2 :: (r •a -> r •b -> r •c) -> ((a -> r) -> (b -> r) -> (c -> r))
lowerK2 f a b = runK (f (K a) (K b))


-- Composition

idK :: r •r
idK = Cat.id


(•<<) :: r •a -> (b -> a) -> r •b
(•<<) = flip contramap

(>>•) :: (b -> a) -> r •a -> r •b
(>>•) = contramap

infixr 1 •<<, >>•

(<<•) :: (r -> s) -> r •a -> s •a
f <<• k = K (f . runK k)

(•>>) :: r •a -> (r -> s) -> s •a
k •>> f = K (f . runK k)

infixr 1 <<•, •>>
