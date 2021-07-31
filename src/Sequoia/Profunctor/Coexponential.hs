{-# LANGUAGE QuantifiedConstraints #-}
module Sequoia.Profunctor.Coexponential
( -- * Coexponential profunctor
  Coexp(recallFn, forgetFn)
  -- * Construction
, (>-)
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
import Fresnel.Lens
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Value

-- Coexponential profunctor

data Coexp e r a b = (:>-) { forgetFn :: a -> r, recallFn :: e -> b }
  deriving (Functor)

infixr 6 :>-

instance Profunctor (Coexp e r) where
  dimap g h = unCoexp (\ f r -> lmap g f >- fmap h r)


-- Construction

(>-) :: a • r -> e ∘ b -> Coexp e r a b
k >- v = coexpFn (k •) (∘ v)

infixr 6 >-

coexpFn :: (a -> r) -> (e -> b) -> Coexp e r a b
coexpFn = (:>-)

idCoexp :: Coexp b a a b
idCoexp = coexpFn id id


-- Elimination

withCoexp :: Coexp e r a b -> (a • r -> e ∘ b -> s) -> s
withCoexp c f = f (forget c) (recall c)

withCoexpFn :: Coexp e r a b -> ((a -> r) -> (e -> b) -> s) -> s
withCoexpFn c = withCoexp c . coerce

runCoexp :: Coexp e r a b -> ((b -> a) -> (e -> r))
runCoexp c = withCoexp c (\ f r -> ((f •) .) . (. (∘ r)))

unCoexp :: (a • r -> e ∘ b -> s) -> Coexp e r a b -> s
unCoexp = flip withCoexp

unCoexpFn :: ((a -> r) -> (e -> b) -> s) -> Coexp e r a b -> s
unCoexpFn = flip withCoexpFn

evalCoexp :: Coexp e r a a -> e ==> r
evalCoexp c = C (\ e -> forget c • e ∘ recall c)

recall :: Coexp e r a b -> e ∘ b
recall = unCoexp (const id)

forget :: Coexp e r a b -> a • r
forget = unCoexp const


-- Optics

recall_ :: Lens (Coexp e r a b) (Coexp e' r a b') (e ∘ b) (e' ∘ b')
recall_ = lens recall (\ s recall -> withCoexp s (const . (>- recall)))

forget_ :: Lens (Coexp e r a b) (Coexp e r' a' b) (a • r) (a' • r')
forget_ = lens forget (\ s forget -> withCoexp s (const (forget >-)))
