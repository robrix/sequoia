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

type Structural e r s = (Weaken e r s, Contract e r s, Exchange e r s)


class Core e r s => Weaken e r s where
  wkL
    ::     _Γ -|s|- _Δ
    -- ---------------
    -> a < _Γ -|s|- _Δ

  wkR
    :: _Γ -|s|- _Δ
    -- ---------------
    -> _Γ -|s|- _Δ > a


wkL'
  :: (Weaken e r s, Exchange e r s)
  => a     < _Γ -|s|- _Δ
  -- -------------------
  -> a < b < _Γ -|s|- _Δ
wkL' = exL . wkL

wkR'
  :: (Weaken e r s, Exchange e r s)
  => _Γ -|s|- _Δ > a
  -- -------------------
  -> _Γ -|s|- _Δ > b > a
wkR' = exR . wkR


class Core e r s => Contract e r s where
  cnL
    :: a < a < _Γ -|s|- _Δ
    -- -------------------
    ->     a < _Γ -|s|- _Δ

  cnR
    :: _Γ -|s|- _Δ > a > a
    -- -------------------
    -> _Γ -|s|- _Δ > a


class Core e r s => Exchange e r s where
  exL
    :: a < b < _Γ -|s|- _Δ
    -- -------------------
    -> b < a < _Γ -|s|- _Δ

  exR
    :: _Γ -|s|- _Δ > a > b
    -- -------------------
    -> _Γ -|s|- _Δ > b > a