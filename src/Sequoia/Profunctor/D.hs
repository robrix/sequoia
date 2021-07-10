{-# LANGUAGE TypeFamilies #-}
module Sequoia.Profunctor.D
( _KV
, KV(..)
, _VK
, VK(..)
, _D
, _DRep
, D(..)
  -- * Optical duality
, _F
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
import           Control.Monad ((<=<))
import           Data.Functor.Contravariant
import           Data.Profunctor
import           Sequoia.Bijection
import           Sequoia.CPS (ContPassing(..))
import           Sequoia.Continuation as K
import           Sequoia.EPS (EnvPassing(..))
import qualified Sequoia.Profunctor.K as Pro
import qualified Sequoia.Profunctor.V as Pro
import           Sequoia.Value as V

_KV :: Optic Iso (KV s r a) (KV s' r' a') (a -> s -> r) (a' -> s' -> r')
_KV = runKV <-> KV

newtype KV s r a = KV { runKV :: a -> s -> r }

instance Cat.Category (KV s) where
  id = KV const
  KV f . KV g = KV (g <=< f)

instance Contravariant (KV s r) where
  contramap f = under _KV (lmap f)

instance K.Representable (KV s r) where
  type Rep (KV s r) = s -> r
  tabulate = KV
  index = runKV

instance Continuation (KV s r)


_VK :: Optic Iso (VK r s a) (VK r' s' a') ((a -> s -> r) -> r) ((a' -> s' -> r') -> r')
_VK = runVK <-> VK

newtype VK r s a = VK { runVK :: (a -> s -> r) -> r }
  deriving (Functor)


_D :: Optic Iso (D r s a b) (D r' s' a' b') ((b -> s -> r) -> (a -> s -> r)) ((b' -> s' -> r') -> (a' -> s' -> r'))
_D = runD <-> D

_DRep :: Optic Iso
  ((b -> s -> r) -> (a -> s -> r))
  ((b' -> s' -> r') -> (a' -> s' -> r'))
  (((a -> s -> r) -> r) -> ((b -> s -> r) -> r))
  (((a' -> s' -> r') -> r') -> ((b' -> s' -> r') -> r'))
_DRep = flip (.) <-> (\ f g a s -> f (\ h -> h a s) g)

newtype D r s a b = D { runD :: (b -> s -> r) -> (a -> s -> r) }
  deriving (Functor)

instance Profunctor (D r s) where
  dimap f g = under _D (dimap (lmap g) (lmap f))

instance Cat.Category (D r s) where
  id = D id
  D f . D g = D (g . f)

instance ContPassing (KV s r) (D r s) where
  inC = D . over _KV
  exC = under _KV . runD

instance Value (VK r s) => EnvPassing (VK r s) (D r s) where
  inE = (_D % _DRep <~) . over _VK
  exE = under _VK . (~> _D % _DRep)


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
