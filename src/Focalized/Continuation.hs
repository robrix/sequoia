module Focalized.Continuation
( -- * Continuations
  type (•)(..)
  -- ** Composition
, idK
, (•<<)
, (>>•)
, (<<•)
, (•>>)
) where

import qualified Control.Category as Cat
import           Data.Functor.Contravariant

-- Continuations

newtype r •a = K { (•) :: a -> r }

infixl 9 •

instance Cat.Category (•) where
  id = K id
  K f . K g = K (g . f)

instance Contravariant ((•) r) where
  contramap f = K . (. f) . (•)


-- Composition

idK :: r •r
idK = Cat.id


(•<<) :: r •a -> (b -> a) -> r •b
(•<<) = flip contramap

(>>•) :: (b -> a) -> r •a -> r •b
(>>•) = contramap

infixr 1 •<<, >>•

(<<•) :: (r -> s) -> r •a -> s •a
f <<• k = K (f . (k •))

(•>>) :: r •a -> (r -> s) -> s •a
k •>> f = K (f . (k •))

infixr 1 <<•, •>>
