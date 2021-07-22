{-# LANGUAGE QuantifiedConstraints #-}
module Sequoia.Profunctor.Coexponential
( -- * Coexponential profunctor
  Coexp(..)
  -- * Coexponential profunctor abstraction
, _Coexponential
, Coexponential(..)
  -- * Construction
, idCoexp
, coexp
  -- * Elimination
, recall
, forget
, runCoexp
, unCoexp
  -- * Coercion
, coerceCoexp
  -- * Optics
, recall_
, forget_
) where

import Data.Functor.Contravariant
import Data.Profunctor
import Sequoia.Functor.Continuation
import Sequoia.Functor.Value
import Sequoia.Optic.Iso
import Sequoia.Optic.Lens

-- Coexponential profunctor

newtype Coexp e r a b = Coexp { withCoexp :: forall s . (V e b -> K r a -> s) -> s }
  deriving (Functor)

instance Profunctor (Coexp e r) where
  dimap g h c = withCoexp c (\ r f -> coexp (fmap h r) (contramap g f))


-- Coexponential profunctor abstraction

_Coexponential :: (Coexponential f, Coexponential f') => Iso (f e r a b) (f' e' r' a' b') (Coexp e r a b) (Coexp e' r' a' b')
_Coexponential = exCoexp `dimap` inCoexp

class (forall e r . Profunctor (f e r)) => Coexponential f where
  inCoexp :: Coexp e r a b -> f e r a b
  exCoexp :: f e r a b -> Coexp e r a b

instance Coexponential Coexp where
  inCoexp = id
  exCoexp = id


-- Construction

idCoexp :: Coexp b a a b
idCoexp = coexp (V id) (K id)

coexp :: V e a -> K r b -> Coexp e r b a
coexp v k = Coexp (\ f -> f v k)


-- Elimination

recall :: Coexp e r a b -> V e b
recall = unCoexp const

forget :: Coexp e r a b -> K r a
forget = unCoexp (const id)

runCoexp :: Coexp e r b a -> ((a -> b) -> (e -> r))
runCoexp c = withCoexp c (\ r f -> ((f •) .) . (. (r ∘)))

unCoexp :: (V e a -> K r b -> s) -> Coexp e r b a -> s
unCoexp = flip withCoexp


-- Coercion

coerceCoexp :: (Coexponential c1, Coexponential c2) => c1 e r a b -> c2 e r a b
coerceCoexp = inCoexp . exCoexp


-- Optics

recall_ :: Lens (Coexp e r a b) (Coexp e' r a b') (V e b) (V e' b')
recall_ = lens recall (\ s recall -> withCoexp s (\ _ forget -> coexp recall forget))

forget_ :: Lens (Coexp e r a b) (Coexp e r' a' b) (K r a) (K r' a')
forget_ = lens forget (\ s forget -> withCoexp s (\ recall _ -> coexp recall forget))
