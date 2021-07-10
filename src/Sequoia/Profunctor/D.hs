{-# LANGUAGE TypeFamilies #-}
module Sequoia.Profunctor.D
( -- * Optical duality
  _F
, F(..)
  -- ** Construction
, inF
, inF'
  -- ** Elimination
, exF
, value
, valueView
, cont
, contView
  -- ** Computation
, (↓)
, (↑)
) where

import           Control.Applicative (liftA2)
import qualified Control.Category as Cat
import           Data.Functor.Contravariant
import           Data.Profunctor
import           Sequoia.Bijection
import           Sequoia.Continuation as K
import qualified Sequoia.Profunctor.K as Pro
import qualified Sequoia.Profunctor.V as Pro
import           Sequoia.Value as V

-- Optical duality

_F :: F k v a b <-> (v a -> v b, k b -> k a)
_F = exF <-> uncurry inF

newtype F k v a b = F { runF :: forall p . Profunctor p => v b `p` k b -> v a `p` k a }

instance (Contravariant k, Functor v) => Profunctor (F k v) where
  dimap f g (F r) = F (dimap (fmap f) (contramap f) . r . dimap (fmap g) (contramap g))

instance Cat.Category (F k v) where
  id = F id
  F f . F g = F (g . f)


-- Construction

inF :: (v s -> v a) -> (k a -> k s) -> F k v s a
inF prj inj = F (dimap prj inj)

inF' :: (K.Representable k, V.Representable v) => (a -> b) -> F k v a b
inF' f = F (dimap (inV1 (f .)) (inK1 (. f)))


-- Elimination

exF :: F k v a b -> (v a -> v b, k b -> k a)
exF = liftA2 (,) value cont

value :: F k v a b -> (v a -> v b)
value = (`valueView` id)

valueView :: F k v a b -> (v b -> r) -> (v a -> r)
valueView f = Pro.runK . runF f . Pro.K

cont :: F k v a b -> (k b -> k a)
cont = (`contView` id)

contView :: F k v a b -> (r -> k b) -> (r -> k a)
contView f = Pro.runV . runF f . Pro.V


-- Computation

(↑) :: F k v a b -> v a -> v b
(↑) = value

infixl 7 ↑

(↓) :: k b -> F k v a b -> k a
k ↓ f = cont f k

infixl 8 ↓
