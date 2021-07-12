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
, evalD
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
_D = exD <-> uncurry inD

newtype D k v a b = D { runD :: Endpoint k v a b }

instance (K.Representable k, V.Representable v) => Profunctor (D k v) where
  dimap f g = D . dimapEndpoint f g . runD

instance (K.Representable k, V.Representable v) => Cat.Category (D k v) where
  id = D (Cat.id, Cat.id)
  D f . D g = D (bimap (fst f Cat..) (snd f Cat..) g)

instance (K.Representable k, V.Representable v) => Functor (D k v a) where
  fmap f = D . dimapEndpoint id f . runD

instance (K.Representable k, V.Representable v) => Applicative (D k v a) where
  pure a = D (pure a, pure a)

  D (fk, fv) <*> D (ak, av) = D (fk <*> ak, fv <*> av)

instance (K.Representable k, V.Representable v) => Monad (D k v c) where
  D (k, v) >>= f = D (k >>= exDK . f, v >>= exDV . f)


type Endpoint k v a b = (C.C k a b, E.E v a b)

dimapEndpoint :: (K.Representable k, V.Representable v) => (a' -> a) -> (b -> b') -> Endpoint k v a b -> Endpoint k v a' b'
dimapEndpoint f g = bimap (dimap f g) (dimap f g)


-- Mixfix notation

type l --|(r :: Type -> Type -> Type) = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Construction

inD :: C.C k a b -> E.E v a b -> a --|D k v|-> b
inD bw fw = D (bw, fw)

inD' :: (K.Representable k, V.Representable v) => (a -> b) -> a --|D k v|-> b
inD' f = inD (C.inC1 (. f)) (E.inE1 (f .))

inDV :: (K.Representable k, V.Representable v) => E.E v a b -> v (a --|D k v|-> b)
inDV f = inV (\ e -> inD (C.inC1 (. dimap const ($ e) (E.exE1 f))) f)

-- FIXME: this is quite limited by the need for the continuation to return locally at b.
inDK :: (K.Representable k, V.Representable v, K.Rep k ~ b) => C.C k a b -> a --|D k v|-> b
inDK f = inD f (E.inE1 (\ a e -> C.exC f (inK id) • e ∘ a))


-- Elimination

exD :: a --|D k v|-> b -> Endpoint k v a b
exD = runD

exDK :: a --|D k v|-> b -> C.C k a b
exDK = fst . exD

exDV :: a --|D k v|-> b -> E.E v a b
exDV = snd . exD


evalD :: K.Representable k => a --|D k v|-> KRep k -> k a
evalD = (idK ↓)


-- Computation

(↑) :: V.Representable v => a --|D k v|-> b -> v a -> v b
(↑) = E.exE . exDV

infixl 7 ↑

(<↑) :: (K.Representable k, V.Representable v, Conj c) => (a `c` _Γ) --|D k v|-> _Δ -> a -> _Γ --|D k v|-> _Δ
f <↑ a = f Cat.<<< inD' (inlr a)

infixl 7 <↑

(↓) :: K.Representable k => k b -> a --|D k v|-> b -> k a
(↓) = flip (C.exC . exDK)

infixl 8 ↓

-- FIXME: this is quite limited by the need for the continuation to return locally at _Δ.
(↓>) :: (K.Representable k, V.Representable v, K.Rep k ~ _Δ, Disj d) => k a -> _Γ --|D k v|-> (_Δ `d` a) -> _Γ --|D k v|-> _Δ
a ↓> f = inD (C.inC (<••> a)) (E.E (fmap (id <--> (a •)))) <<< f

infixr 9 ↓>
