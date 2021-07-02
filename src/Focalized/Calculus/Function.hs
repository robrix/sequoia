module Focalized.Calculus.Function
( -- * Function
  FunctionIntro(..)
, funL2
, ($$)
, funR'
  -- * Connectives
, module Focalized.Connective.Function
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Connective.Function
import Focalized.Polarity
import Prelude hiding (init)

-- Function

class FunctionIntro s where
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
  :: (Core s, FunctionIntro s, Pos a, Neg b)
  -- ---------------------------------
  => a ~~r~> b < a < _Γ -|s r|- _Δ > b
funL2 = funL init init

($$)
  :: (Weaken s, Exchange s, FunctionIntro s, Pos a, Neg b)
  => _Γ -|s r|- _Δ > a ~~r~> b   ->   _Γ -|s r|- _Δ > a
  -- --------------------------------------------------
  ->                _Γ -|s r|- _Δ > b
f $$ a = wkR' f >>> wkR' a `funL` init

funR'
  :: (Weaken s, Exchange s, FunctionIntro s, Pos a, Neg b)
  =>     _Γ -|s r|- _Δ > a ~~r~> b
  -- -----------------------------
  -> a < _Γ -|s r|- _Δ > b
funR' p = wkL (wkR' p) >>> funL2
