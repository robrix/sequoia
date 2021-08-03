{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Calculus.Structural
(  -- * Structural
  Structural
, Weaken(..)
, wkL'
, wkR'
, Contract(..)
, Exchange(..)
  -- * Profunctorial structural rules
, weakenL
, weakenR
, contractL
, contractR
, exchangeL
, exchangeR
  -- * Derivation
, Profunctorially(..)
) where

import Data.Bifunctor
import Data.Profunctor
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Conjunction
import Sequoia.Disjunction
import Sequoia.Profunctor.Diagonal

-- Structural

type Structural s = (Weaken s, Contract s, Exchange s)


class Core s => Weaken s where
  wkL
    ::     _Γ -|s e r|- _Δ
    -- -------------------
    -> a < _Γ -|s e r|- _Δ

  wkR
    :: _Γ -|s e r|- _Δ
    -- -------------------
    -> _Γ -|s e r|- _Δ > a


wkL'
  :: (Weaken s, Exchange s)
  => a     < _Γ -|s e r|- _Δ
  -- -----------------------
  -> a < b < _Γ -|s e r|- _Δ
wkL' = exL . wkL

wkR'
  :: (Weaken s, Exchange s)
  => _Γ -|s e r|- _Δ > a
  -- -----------------------
  -> _Γ -|s e r|- _Δ > b > a
wkR' = exR . wkR


class Core s => Contract s where
  cnL
    :: a < a < _Γ -|s e r|- _Δ
    -- -----------------------
    ->     a < _Γ -|s e r|- _Δ

  cnR
    :: _Γ -|s e r|- _Δ > a > a
    -- -----------------------
    -> _Γ -|s e r|- _Δ > a


class Core s => Exchange s where
  exL
    :: a < b < _Γ -|s e r|- _Δ
    -- -----------------------
    -> b < a < _Γ -|s e r|- _Δ

  exR
    :: _Γ -|s e r|- _Δ > a > b
    -- -----------------------
    -> _Γ -|s e r|- _Δ > b > a


-- Profunctorial structural rules

weakenL :: Profunctor p => p a b -> p (c, a) b
weakenL = lmap exr

weakenR :: (Profunctor p, Disj t) => p a b -> p a (b `t` c)
weakenR = rmap inl


contractL :: (Profunctor p, Conj t) => p (a `t` a) b -> p a b
contractL = lmap dupConj

contractR :: (Profunctor p, Disj t) => p a (b `t` b) -> p a b
contractR = rmap dedupDisj


exchangeL :: (Profunctor p, Conj t) => p (a `t` c) b -> p (c `t` a) b
exchangeL = lmap swapConj

exchangeR :: (Profunctor p, Disj t) => p a (b `t` c) -> p a (c `t` b)
exchangeR = rmap mirrorDisj


-- Derivation

newtype Profunctorially s e r a b = Profunctorially { runProfunctorially :: s e r a b }
  deriving (Core, Profunctor)

instance Profunctor (s e r) => Functor (Profunctorially s e r a) where
  fmap = rmap

instance (Core s, forall e r . Profunctor (s e r)) => Weaken (Profunctorially s) where
  wkL = lmap exr
  wkR = rmap inl

instance (Core s, forall e r . Profunctor (s e r)) => Contract (Profunctorially s) where
  cnL = lmap (exl >---< id)
  cnR = rmap (id <--> inr)

instance (Core s, forall e r . Profunctor (s e r)) => Exchange (Profunctorially s) where
  exL = lmap (exl . exr >---< second exr)
  exR = rmap (first inl <--> inl . inr)
