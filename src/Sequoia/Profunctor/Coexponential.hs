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
, runCoexp
, withCoexp
  -- * Optics
, recall_
, forget_
) where

import Data.Profunctor
import Sequoia.Confunctor
import Sequoia.Functor.K
import Sequoia.Functor.V
import Sequoia.Optic.Optic

-- Coexponential profunctor

data Coexp e r a b = Coexp { recall :: V e b, forget :: K r a }
  deriving (Functor)

instance Profunctor (Coexp e r) where
  dimap g h c = withCoexp c (\ r f -> coexp (h . r) (f . g))


-- Coexponential profunctor abstraction

_Coexponential :: (Coexponential f, Coexponential f', Profunctor p) => Optic p (f e r a b) (f' e' r' a' b') (Coexp e r b a) (Coexp e' r' b' a')
_Coexponential = exCS `dimap` inCS

class (forall e r . Confunctor (f e r)) => Coexponential f where
  inCS :: Coexp e r b a -> f e r a b
  exCS :: f e r a b -> Coexp e r b a


-- Construction

idCoexp :: Coexp b a a b
idCoexp = coexp id id

coexp :: (e -> a) -> (b -> r) -> Coexp e r b a
coexp r f = Coexp (V r) (K f)


-- Elimination

runCoexp :: Coexp e r b a -> ((a -> b) -> (e -> r))
runCoexp c = withCoexp c (\ r f -> (f .) . (. r))

withCoexp :: Coexp e r b a -> (((e -> a) -> (b -> r) -> s) -> s)
withCoexp c f = f (runV (recall c)) (runK (forget c))


-- Optics

type Lens s t a b = (forall p . Strong p => p a b -> p s t)

recall_ :: Lens (Coexp e r a b) (Coexp e' r a b') (V e b) (V e' b')
recall_ = lens recall (\ s recall -> s{ recall })

forget_ :: Lens (Coexp e r a b) (Coexp e r' a' b) (K r a) (K r' a')
forget_ = lens forget (\ s forget -> s{ forget })

lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens prj inj = dimap (\ s -> (prj s, s)) (\ (b, s) -> inj s b) . first'
