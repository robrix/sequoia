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

import           Control.Applicative (liftA2)
import           Control.Arrow ((***))
import           Control.Category ((<<<), (>>>))
import qualified Control.Category as Cat
import           Data.Bifunctor (bimap)
import           Data.Functor.Contravariant
import           Data.Kind (Type)
import           Data.Profunctor
import           Sequoia.Bijection
import qualified Sequoia.CPS as C
import           Sequoia.Conjunction
import           Sequoia.Continuation as K
import           Sequoia.Disjunction
import qualified Sequoia.EPS as E
import           Sequoia.Value as V

-- Dual profunctor

_D :: a --|D k v|-> b <-> (C.C k a b, E.E v a b)
_D = (C.C *** E.E) . exD <-> uncurry inD . (C.runC *** E.runE)

newtype D k v a b = D { runD :: Endpoint k v a b }

instance (Contravariant k, Functor v) => Profunctor (D k v) where
  dimap f g = D . dimapEndpoint f g . runD

instance Cat.Category (D k v) where
  id = D (id, id)
  D f . D g = D (fst g . fst f, snd f . snd g)

instance (Contravariant k, Functor v) => Functor (D k v a) where
  fmap f = D . dimapEndpoint id f . runD

instance (K.Representable k, V.Representable v) => Applicative (D k v a) where
  pure a = D (\ ka -> inK (const (ka • a)), const (inV0 a))

  f <*> a = D (let (k', v') = runD f ; (k'', v'') = runD a in (liftK2K2 ($) k' k'', liftA2 (liftV2 ($)) v' v''))

instance (K.Representable k, V.Representable v) => Monad (D k v c) where
  D (k, v) >>= f = D
    ( inK . \ b c -> k (inK (\ a -> exDK (f a) b • c)) • c
    , inV . \ c e -> e ∘ exDV (f (e ∘ v c)) c)


type Endpoint k v a b = (k b -> k a, v a -> v b)

dimapEndpoint :: (Contravariant k, Functor v) => (a' -> a) -> (b -> b') -> Endpoint k v a b -> Endpoint k v a' b'
dimapEndpoint f g = bimap (dimap (contramap g) (contramap f)) (dimap (fmap f) (fmap g))


-- Mixfix notation

type l --|(r :: Type -> Type -> Type) = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Construction

inD :: (k b -> k a) -> (v a -> v b) -> a --|D k v|-> b
inD bw fw = D (bw, fw)

inD' :: (K.Representable k, V.Representable v) => (a -> b) -> a --|D k v|-> b
inD' f = inD (inK1 (. f)) (inV1 (f .))

inDV :: (K.Representable k, V.Representable v) => (v a -> v b) -> v (a --|D k v|-> b)
inDV f = inV (\ e -> inD (inK1 (. dimap const ($ e) (exV1 f))) f)

-- FIXME: this is quite limited by the need for the continuation to return locally at b.
inDK :: (K.Representable k, V.Representable v, K.Rep k ~ b) => (k b -> k a) -> a --|D k v|-> b
inDK f = inD f (inV1 (\ a e -> f (inK id) • e ∘ a))


-- Elimination

exD :: a --|D k v|-> b -> (k b -> k a, v a -> v b)
exD = runD

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
