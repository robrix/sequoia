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
, inD1
, inD1'
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
import           Sequoia.CPS hiding ((↓), (↓>))
import           Sequoia.Conjunction
import           Sequoia.Continuation as K
import           Sequoia.Disjunction
import           Sequoia.EPS hiding ((<↑), (↑))
import           Sequoia.Functor.K
import           Sequoia.Functor.V
import           Sequoia.Value as V

-- Dual profunctor

_D :: a --|D r s|-> b <-> (C (K r) a b, E (V s) a b)
_D = exD <-> uncurry inD

newtype D r s a b = D { runD :: Endpoint r s a b }

instance Profunctor (D r s) where
  dimap f g = D . dimapEndpoint f g . runD

instance Cat.Category (D r s) where
  id = D (Cat.id, Cat.id)
  D f . D g = D (bimap (fst f Cat..) (snd f Cat..) g)

instance Functor (D r s a) where
  fmap f = D . dimapEndpoint id f . runD

instance Applicative (D r s a) where
  pure a = D (pure a, pure a)

  D (fk, fv) <*> D (ak, av) = D (fk <*> ak, fv <*> av)

instance Monad (D r s c) where
  D (k, v) >>= f = D (k >>= exDK . f, v >>= exDV . f)


type Endpoint r s a b = (C (K r) a b, E (V s) a b)

dimapEndpoint :: (a' -> a) -> (b -> b') -> Endpoint r s a b -> Endpoint r s a' b'
dimapEndpoint f g = bimap (dimap f g) (dimap f g)


-- Mixfix notation

type l --|(r :: Type -> Type -> Type) = r l
type l|-> r = l r

infixr 6 --|
infixr 5 |->


-- Construction

inD :: C (K r) a b -> E (V s) a b -> a --|D r s|-> b
inD bw fw = D (bw, fw)

inD1 :: ((b -> r) -> (a -> r)) -> ((s -> a) -> (s -> b)) -> a --|D r s|-> b
inD1 k v = inD (inC1 k) (inE1 v)

inD1' :: (K r b -> (a -> r)) -> (V s a -> (s -> b)) -> a --|D r s|-> b
inD1' k v = inD (inC1' k) (inE1' v)

inD' :: (a -> b) -> a --|D r s|-> b
inD' f = inD (inC1 (. f)) (inE1 (f .))

inDV :: E (V s) a b -> V s (a --|D r s|-> b)
inDV f = inV (\ e -> inD (inC1 (. dimap const ($ e) (exE1 f))) f)

-- FIXME: this is quite limited by the need for the continuation to return locally at b.
inDK :: C (K b) a b -> a --|D b s|-> b
inDK f = inD f (inE1 (\ a e -> exC f (inK id) • e ∘ a))


-- Elimination

exD :: a --|D r s|-> b -> Endpoint r s a b
exD = runD

exDK :: a --|D r s|-> b -> C (K r) a b
exDK = fst . exD

exDV :: a --|D r s|-> b -> E (V s) a b
exDV = snd . exD


evalD :: a --|D r s|-> r -> K r a
evalD = (idK ↓)


-- Computation

(↑) :: a --|D r s|-> b -> V s a -> V s b
(↑) = exE . exDV

infixl 7 ↑

(<↑) :: Conj c => (a `c` _Γ) --|D r s|-> _Δ -> a -> _Γ --|D r s|-> _Δ
f <↑ a = f Cat.<<< inD' (inlr a)

infixl 7 <↑

(↓) :: K r b -> a --|D r s|-> b -> K r a
(↓) = flip (exC . exDK)

infixl 8 ↓

-- FIXME: this is quite limited by the need for the continuation to return locally at _Δ.
(↓>) :: Disj d => K _Δ a -> _Γ --|D _Δ s|-> (_Δ `d` a) -> _Γ --|D _Δ s|-> _Δ
a ↓> f = inD (inC (<••> a)) (inE (fmap (id <--> (a •)))) <<< f

infixr 9 ↓>
