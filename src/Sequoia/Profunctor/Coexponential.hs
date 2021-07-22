{-# LANGUAGE QuantifiedConstraints #-}
module Sequoia.Profunctor.Coexponential
( -- * Coexponential profunctor
  Coexp(..)
  -- * Coexponential profunctor abstraction
, Coexponential(..)
  -- * Construction
, idCoexp
, coexp
  -- * Elimination
, recall
, forget
, runCoexp
, unCoexp
  -- * Optics
, recall_
, forget_
) where

import Data.Profunctor
import Sequoia.Optic.Lens
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Value

-- Coexponential profunctor

newtype Coexp e r a b = Coexp { withCoexp :: forall s . (e ∘ b -> a • r -> s) -> s }
  deriving (Functor)

instance Profunctor (Coexp e r) where
  dimap g h c = withCoexp c (\ r f -> coexp (fmap h r) (lmap g f))


-- Coexponential profunctor abstraction

class (forall e r . Profunctor (f e r)) => Coexponential f where
  inCoexp :: Coexp e r a b -> f e r a b
  exCoexp :: f e r a b -> Coexp e r a b


-- Construction

idCoexp :: Coexp b a a b
idCoexp = coexp (V id) (K id)

coexp :: e ∘ a -> b • r -> Coexp e r b a
coexp v k = Coexp (\ f -> f v k)


-- Elimination

recall :: Coexp e r a b -> e ∘ b
recall = unCoexp const

forget :: Coexp e r a b -> a • r
forget = unCoexp (const id)

runCoexp :: Coexp e r b a -> ((a -> b) -> (e -> r))
runCoexp c = withCoexp c (\ r f -> ((f •) .) . (. (r ∘)))

unCoexp :: (e ∘ a -> b • r -> s) -> Coexp e r b a -> s
unCoexp = flip withCoexp


-- Optics

recall_ :: Lens (Coexp e r a b) (Coexp e' r a b') (e ∘ b) (e' ∘ b')
recall_ = lens recall (\ s recall -> withCoexp s (\ _ forget -> coexp recall forget))

forget_ :: Lens (Coexp e r a b) (Coexp e r' a' b) (a • r) (a' • r')
forget_ = lens forget (\ s forget -> withCoexp s (\ recall _ -> coexp recall forget))
