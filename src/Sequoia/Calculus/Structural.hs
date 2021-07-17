{-# LANGUAGE ConstraintKinds #-}
module Sequoia.Calculus.Structural
(  -- * Structural
  Structural
, Weaken(..)
, wkL'
, wkR'
, Contract(..)
, Exchange(..)
) where

import Sequoia.Calculus.Context
import Sequoia.Calculus.Core

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
