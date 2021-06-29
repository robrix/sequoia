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

class Implication s where
  funL
    :: (Pos a, Neg b)
    => _Γ -|s r|- _Δ > a   ->   b < _Γ -|s r|- _Δ
    -- ------------------------------------------
    ->        a ~~r~> b < _Γ -|s r|- _Δ

  funR
    :: (Pos a, Neg b)
    => a < _Γ -|s r|- _Δ > b
    -- -----------------------------
    ->     _Γ -|s r|- _Δ > a ~~r~> b


funL2
  :: (Core s, Implication s, Pos a, Neg b)
  -- ---------------------------------
  => a ~~r~> b < a < _Γ -|s r|- _Δ > b
funL2 = funL init init

($$)
  :: (Weaken s, Exchange s, Implication s, Pos a, Neg b)
  => _Γ -|s r|- _Δ > a ~~r~> b   ->   _Γ -|s r|- _Δ > a
  -- --------------------------------------------------
  ->                _Γ -|s r|- _Δ > b
f $$ a = wkR' f >>> wkR' a `funL` init

funR'
  :: (Weaken s, Exchange s, Implication s, Pos a, Neg b)
  =>     _Γ -|s r|- _Δ > a ~~r~> b
  -- -----------------------------
  -> a < _Γ -|s r|- _Δ > b
funR' p = wkL (wkR' p) >>> funL2
