{-# LANGUAGE ConstraintKinds #-}
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
) where

import Data.Profunctor
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
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
weakenL = lmap snd

weakenR :: Profunctor p => p a b -> p a (Either b c)
weakenR = rmap Left


contractL :: Profunctor p => p (a, a) b -> p a b
contractL = lmap dup

contractR :: Profunctor p => p a (Either b b) -> p a b
contractR = rmap dedup


exchangeL :: Profunctor p => p (a, c) b -> p (c, a) b
exchangeL = lmap swap

exchangeR :: Profunctor p => p a (Either b c) -> p a (Either c b)
exchangeR = rmap mirror
