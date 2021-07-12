{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
module Sequoia.Profunctor.D
( -- * Dual profunctor
  _D
, D(..)
  -- ** Mixfix notation
, type (--|)
, type (|->)
  -- ** Construction
, inD
, inD'
, inDV
, inDK
  -- ** Elimination
, exD
, exDV
, exDK
  -- ** Composition
, (<<<)
, (>>>)
  -- ** Computation
, (↑)
, (<↑)
, (↓)
, (↓>)
) where

import           Control.Category ((<<<), (>>>))
import qualified Control.Category as Cat
import           Data.Bifunctor (bimap)
import           Data.Functor.Contravariant
import           Data.Kind (Type)
import           Data.Profunctor
import           Sequoia.Bijection
import           Sequoia.Conjunction
import           Sequoia.Continuation as K
import           Sequoia.Disjunction
import           Sequoia.Value as V

-- Dual profunctor

_D :: a --|D k v|-> b <-> (k b -> k a, v a -> v b)
_D = exD <-> uncurry inD

newtype D k v a b = D { runD :: forall r s . Endpoint r s k v a -> Endpoint r s k v b }

instance (Contravariant k, Functor v) => Profunctor (D k v) where
  dimap f g (D r) = D (mapEndpoint g . r . mapEndpoint f)

instance Cat.Category (D k v) where
  id = D id
  D f . D g = D (f . g)

instance (Contravariant k, Functor v) => Functor (D k v a) where
  fmap f (D r) = D (mapEndpoint f . r)


type Endpoint r s k v a = (k a -> r, s -> v a)

mapEndpoint :: (Contravariant k, Functor v) => (a -> b) -> Endpoint r s k v a -> Endpoint r s k v b
mapEndpoint f = bimap (lmap (contramap f)) (rmap (fmap f))


-- Mixfix notation

type l --|(r :: Type -> Type -> Type) = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Construction

inD :: (k b -> k a) -> (v a -> v b) -> a --|D k v|-> b
inD bw fw = D (bimap (lmap bw) (rmap fw))

inD' :: (K.Representable k, V.Representable v) => (a -> b) -> a --|D k v|-> b
inD' f = inD (inK1 (. f)) (inV1 (f .))

inDV :: (K.Representable k, V.Representable v) => (v a -> v b) -> v (a --|D k v|-> b)
inDV f = inV (\ e -> inD (inK1 (. dimap const ($ e) (exV1 f))) f)

-- FIXME: this is quite limited by the need for the continuation to return locally at b.
inDK :: (K.Representable k, V.Representable v, K.Rep k ~ b) => (k b -> k a) -> a --|D k v|-> b
inDK f = inD f (inV1 (\ a e -> f (inK id) • e ∘ a))


-- Elimination

exD :: a --|D k v|-> b -> (k b -> k a, v a -> v b)
exD f = runD f (id, id)

exDK :: a --|D k v|-> b -> (k b -> k a)
exDK = fst . exD

exDV :: a --|D k v|-> b -> (v a -> v b)
exDV = snd . exD


-- Computation

(↑) :: a --|D k v|-> b -> v a -> v b
(↑) = exDV

infixl 7 ↑

(<↑) :: (K.Representable k, V.Representable v, Conj c) => (a `c` _Γ) --|D k v|-> _Δ -> a -> _Γ --|D k v|-> _Δ
f <↑ a = f Cat.<<< inD' (inlr a)

infixl 7 <↑

(↓) :: k b -> a --|D k v|-> b -> k a
(↓) = flip exDK

infixl 8 ↓

-- FIXME: this is quite limited by the need for the continuation to return locally at _Δ.
(↓>) :: (K.Representable k, Functor v, K.Rep k ~ _Δ, Disj d) => k a -> _Γ --|D k v|-> (_Δ `d` a) -> _Γ --|D k v|-> _Δ
a ↓> f = inD (<••> a) (fmap (id <--> (a •))) <<< f

infixr 9 ↓>
