{-# LANGUAGE FunctionalDependencies #-}
module Focalized.Calculus.Function
( -- * Implication
  Implication(..)
, funL2
, ($$)
, funR'
  -- * Connectives
, module Focalized.Function
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Function
import Focalized.Polarity
import Prelude hiding (init)

-- Implication

class Implication r s | s -> r where
  funL
    :: (Pos a, Neg b)
    => _Γ -|s|- _Δ > a   ->   b < _Γ -|s|- _Δ
    -- --------------------------------------
    ->        a ~~r~> b < _Γ -|s|- _Δ

  funR
    :: (Pos a, Neg b)
    => a < _Γ -|s|- _Δ > b
    -- ---------------------------
    ->     _Γ -|s|- _Δ > a ~~r~> b


funL2
  :: (Core s, Implication r s, Pos a, Neg b)
  -- -------------------------------
  => a ~~r~> b < a < _Γ -|s|- _Δ > b
funL2 = funL init init

($$)
  :: (Weaken s, Exchange s, Implication r s, Pos a, Neg b)
  => _Γ -|s|- _Δ > a ~~r~> b   ->   _Γ -|s|- _Δ > a
  -- ----------------------------------------------
  ->                _Γ -|s|- _Δ > b
f $$ a = wkR' f >>> wkR' a `funL` init

funR'
  :: (Weaken s, Exchange s, Implication r s, Pos a, Neg b)
  =>     _Γ -|s|- _Δ > a ~~r~> b
  -- ---------------------------
  -> a < _Γ -|s|- _Δ > b
funR' p = wkL (wkR' p) >>> funL2
