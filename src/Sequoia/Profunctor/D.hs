{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
module Sequoia.Profunctor.D
( -- * Dual profunctor
  _D
, D(..)
  -- * Dual profunctor abstraction
, Dual(..)
  -- ** Construction
, inD'
  -- ** Elimination
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

-- Dual profunctor

_D :: Dual k v f => f a b <-> (v a -> v b, k b -> k a)
_D = exD <-> uncurry inD

newtype D k v a b = D { runD :: forall p . Profunctor p => v b `p` k b -> v a `p` k a }

instance (Contravariant k, Functor v) => Profunctor (D k v) where
  dimap f g (D r) = D (dimap (fmap f) (contramap f) . r . dimap (fmap g) (contramap g))

instance Cat.Category (D k v) where
  id = D id
  D f . D g = D (g . f)


-- Dual profunctor abstraction

class (Continuation k, Value v, Cat.Category f, Profunctor f) => Dual k v f | f -> k v where
  inD :: (v a -> v b) -> (k b -> k a) -> f a b
  exD :: f a b -> (v a -> v b, k b -> k a)

instance (Continuation k, Value v) => Dual k v (D k v) where
  inD fw bw = D (dimap fw bw)
  exD = liftA2 (,) value cont


-- Construction

inD' :: (K.Representable k, V.Representable v) => (a -> b) -> D k v a b
inD' f = D (dimap (inV1 (f .)) (inK1 (. f)))


-- Elimination

value :: D k v a b -> (v a -> v b)
value = (`valueView` id)

valueView :: D k v a b -> (v b -> r) -> (v a -> r)
valueView f = Pro.runK . runD f . Pro.K

cont :: D k v a b -> (k b -> k a)
cont = (`contView` id)

contView :: D k v a b -> (r -> k b) -> (r -> k a)
contView f = Pro.runV . runD f . Pro.V


-- Computation

(↑) :: D k v a b -> v a -> v b
(↑) = value

infixl 7 ↑

(↓) :: k b -> D k v a b -> k a
(↓) = flip cont

infixl 8 ↓
