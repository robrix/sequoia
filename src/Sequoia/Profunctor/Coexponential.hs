{-# LANGUAGE QuantifiedConstraints #-}
module Sequoia.Profunctor.Coexponential
( -- * Coexponential profunctor
  Coexp(recallFn, forgetFn)
  -- * Construction
, coexp
, coexpFn
, idCoexp
  -- * Elimination
, withCoexpFn
, withCoexp
, runCoexp
, unCoexp
, unCoexpFn
, evalCoexp
, recall
, forget
  -- * Optics
, recall_
, forget_
) where

import Data.Coerce
import Data.Profunctor
import Sequoia.Optic.Lens
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Value

-- Coexponential profunctor

data Coexp e r a b = Coexp { recallFn :: e -> b, forgetFn :: a -> r }
  deriving (Functor)

instance Profunctor (Coexp e r) where
  dimap g h = unCoexp (\ r f -> coexp (fmap h r) (lmap g f))


-- Construction

coexp :: e ∘ b -> a • r -> Coexp e r a b
coexp v k = coexpFn (v ∘) (k •)

coexpFn :: (e -> b) -> (a -> r) -> Coexp e r a b
coexpFn = Coexp

idCoexp :: Coexp b a a b
idCoexp = coexpFn id id


-- Elimination

withCoexp :: Coexp e r a b -> (e ∘ b -> a • r -> s) -> s
withCoexp c f = f (recall c) (forget c)

withCoexpFn :: Coexp e r a b -> ((e -> b) -> (a -> r) -> s) -> s
withCoexpFn c = withCoexp c . coerce

runCoexp :: Coexp e r b a -> ((a -> b) -> (e -> r))
runCoexp c = withCoexp c (\ r f -> ((f •) .) . (. (r ∘)))

unCoexp :: (e ∘ b -> a • r -> s) -> Coexp e r a b -> s
unCoexp = flip withCoexp

unCoexpFn :: ((e -> b) -> (a-> r) -> s) -> Coexp e r a b -> s
unCoexpFn = flip withCoexpFn

evalCoexp :: Coexp e r a a -> e ==> r
evalCoexp c = C (\ e -> forget c • recall c ∘ e)

recall :: Coexp e r a b -> e ∘ b
recall = unCoexp const

forget :: Coexp e r a b -> a • r
forget = unCoexp (const id)


-- Optics

recall_ :: Lens (Coexp e r a b) (Coexp e' r a b') (e ∘ b) (e' ∘ b')
recall_ = lens recall (\ s recall -> withCoexp s (const (coexp recall)))

forget_ :: Lens (Coexp e r a b) (Coexp e r' a' b) (a • r) (a' • r')
forget_ = lens forget (\ s forget -> withCoexp s (const . (`coexp` forget)))
