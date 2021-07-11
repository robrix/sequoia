{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
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
, viewV
, viewK
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
import           Data.Functor.Contravariant
import           Data.Profunctor
import           Sequoia.Bijection
import           Sequoia.Conjunction
import           Sequoia.Continuation as K
import           Sequoia.Disjunction
import qualified Sequoia.Profunctor.K as Pro
import           Sequoia.Profunctor.Product
import qualified Sequoia.Profunctor.V as Pro
import           Sequoia.Value as V

-- Dual profunctor

_D :: a --|D k v|-> b <-> (v a -> v b, k b -> k a)
_D = exD <-> uncurry inD

newtype D k v a b = D { runD :: forall p . Profunctor p => k a `p` v a -> k b `p` v b }

instance (Contravariant k, Functor v) => Profunctor (D k v) where
  dimap f g (D r) = D (dimap (contramap g) (fmap g) . r . dimap (contramap f) (fmap f))

instance Cat.Category (D k v) where
  id = D id
  D f . D g = D (f . g)


-- Mixfix notation

type l --|r = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Construction

inD :: (v a -> v b) -> (k b -> k a) -> a --|D k v|-> b
inD fw bw = D (dimap bw fw)

inD' :: (K.Representable k, V.Representable v) => (a -> b) -> a --|D k v|-> b
inD' f = inD (inV1 (f .)) (inK1 (. f))

inDV :: (K.Representable k, V.Representable v) => (v a -> v b) -> v (a --|D k v|-> b)
inDV f = inV (\ e -> inD f (inK1 (. dimap const ($ e) (exV1 f))))

-- FIXME: this is quite limited by the need for the continuation to return locally at b.
inDK :: (K.Representable k, V.Representable v, K.Rep k ~ b) => (k b -> k a) -> k **(a --|D k v|-> b)
inDK f = inK (\ k -> k • inD (inV1 (\ a e -> f (inK id) • e ∘ a)) f)


-- Elimination

exD :: a --|D k v|-> b -> (v a -> v b, k b -> k a)
exD f = let (Pro.V v, Pro.K k) = runProduct (runD f (Product (Pro.V id, Pro.K id))) in (v, k)

exDV :: a --|D k v|-> b -> (v a -> v b)
exDV = fst . exD

exDK :: a --|D k v|-> b -> (k b -> k a)
exDK = snd . exD

viewV :: D k v a b -> (s -> v a) -> (s -> v b)
viewV f = Pro.runV . runD f . Pro.V

viewK :: D k v a b -> (k a -> r) -> (k b -> r)
viewK f = Pro.runK . runD f . Pro.K


-- Computation

(↑) :: a --|D k v|-> b -> v a -> v b
(↑) = fst . exD

infixl 7 ↑

(<↑) :: (K.Representable k, V.Representable v) => Conj c => (a `c` _Γ) --|D k v|-> _Δ -> a -> _Γ --|D k v|-> _Δ
f <↑ a = f Cat.<<< inD' (inlr a)

infixl 7 <↑

(↓) :: k b -> a --|D k v|-> b -> k a
(↓) = flip (snd . exD)

infixl 8 ↓

-- FIXME: this is quite limited by the need for the continuation to return locally at _Δ.
(↓>) :: (K.Representable k, Functor v, K.Rep k ~ _Δ) => Disj d => k a -> _Γ --|D k v|-> (_Δ `d` a) -> _Γ --|D k v|-> _Δ
a ↓> f = inD (fmap (id <--> (a •))) (<••> a) <<< f

infixr 9 ↓>
