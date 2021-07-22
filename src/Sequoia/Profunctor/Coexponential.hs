{-# LANGUAGE QuantifiedConstraints #-}
module Sequoia.Profunctor.Coexponential
( -- * Coexponential profunctor
  Coexp(..)
  -- * Construction
, idCoexp
, coexp
  -- * Elimination
, recall
, forget
, withCoexp
, runCoexp
, unCoexp
  -- * Optics
, recall_
, forget_
) where

import Data.Coerce
import Data.Profunctor
import Sequoia.Optic.Lens
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Value

-- Coexponential profunctor

newtype Coexp e r a b = Coexp { getCoexp :: forall s . ((e -> b) -> (a -> r) -> s) -> s }
  deriving (Functor)

instance Profunctor (Coexp e r) where
  dimap g h c = withCoexp c (\ r f -> coexp (fmap h r) (lmap g f))


-- Construction

idCoexp :: Coexp b a a b
idCoexp = coexp (V id) (K id)

coexp :: e ∘ a -> b • r -> Coexp e r b a
coexp v k = Coexp (\ f -> f (v ∘) (k •))


-- Elimination

recall :: Coexp e r a b -> e ∘ b
recall = unCoexp const

forget :: Coexp e r a b -> a • r
forget = unCoexp (const id)

withCoexp :: Coexp e r a b -> (e ∘ b -> a • r -> s) -> s
withCoexp c = getCoexp c . coerce

runCoexp :: Coexp e r b a -> ((a -> b) -> (e -> r))
runCoexp c = withCoexp c (\ r f -> ((f •) .) . (. (r ∘)))

unCoexp :: (e ∘ a -> b • r -> s) -> Coexp e r b a -> s
unCoexp = flip withCoexp


-- Optics

recall_ :: Lens (Coexp e r a b) (Coexp e' r a b') (e ∘ b) (e' ∘ b')
recall_ = lens recall (\ s recall -> withCoexp s (\ _ forget -> coexp recall forget))

forget_ :: Lens (Coexp e r a b) (Coexp e r' a' b) (a • r) (a' • r')
forget_ = lens forget (\ s forget -> withCoexp s (\ recall _ -> coexp recall forget))
