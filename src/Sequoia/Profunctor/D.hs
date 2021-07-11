{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
module Sequoia.Profunctor.D
( -- * Dual profunctor
  D(..)
  -- * Dual profunctor abstraction
, Dual(..)
  -- ** Mixfix notation
, type (--|)
, type (|->)
  -- ** Construction
, inD'
  -- ** Elimination
, exDV
, exDK
, viewV
, viewK
  -- ** Computation
, (↑)
, (<↑)
, (↓)
) where

import           Control.Applicative (liftA2)
import qualified Control.Category as Cat
import           Data.Functor.Contravariant
import           Data.Profunctor
import           Sequoia.Bijection
import           Sequoia.Conjunction
import           Sequoia.Continuation as K
import qualified Sequoia.Profunctor.K as Pro
import qualified Sequoia.Profunctor.V as Pro
import           Sequoia.Value as V

-- Dual profunctor

newtype D k v a b = D { runD :: forall p . Profunctor p => k a `p` v a -> k b `p` v b }

instance (Contravariant k, Functor v) => Profunctor (D k v) where
  dimap f g (D r) = D (dimap (contramap g) (fmap g) . r . dimap (contramap f) (fmap f))

instance Cat.Category (D k v) where
  id = D id
  D f . D g = D (f . g)


-- Dual profunctor abstraction

class (Continuation k, Value v, Cat.Category f, Profunctor f) => Dual k v f | f -> k v where
  {-# MINIMAL _D | (inD, exD) #-}
  _D :: a --|f|-> b <-> (v a -> v b, k b -> k a)
  _D = exD <-> uncurry inD

  inD :: (v a -> v b) -> (k b -> k a) -> a --|f|-> b
  inD = curry (_D <~)
  exD :: a --|f|-> b -> (v a -> v b, k b -> k a)
  exD = (~> _D)

instance (Continuation k, Value v) => Dual k v (D k v) where
  inD fw bw = D (dimap bw fw)
  exD = liftA2 (,) (`viewV` id) (`viewK` id)


-- Mixfix notation

type l --|r = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Construction

inD' :: Dual k v f => (a -> b) -> a --|f|-> b
inD' f = inD (inV1 (f .)) (inK1 (. f))


-- Elimination

exDV :: Dual k v f => a --|f|-> b -> (v a -> v b)
exDV = fst . exD

exDK :: Dual k v f => a --|f|-> b -> (k b -> k a)
exDK = snd . exD

viewV :: D k v a b -> (s -> v a) -> (s -> v b)
viewV f = Pro.runV . runD f . Pro.V

viewK :: D k v a b -> (k a -> r) -> (k b -> r)
viewK f = Pro.runK . runD f . Pro.K


-- Computation

(↑) :: Dual k v f => a --|f|-> b -> v a -> v b
(↑) = fst . exD

infixl 7 ↑

(<↑) :: (Dual k v f, Conj c) => (a `c` _Γ) --|f|-> _Δ -> a -> _Γ --|f|-> _Δ
f <↑ a = inD (exDV f . fmap (inlr a)) (contramap (inlr a) . exDK f)

infixl 7 <↑

(↓) :: Dual k v f => k b -> a --|f|-> b -> k a
(↓) = flip (snd . exD)

infixl 8 ↓
