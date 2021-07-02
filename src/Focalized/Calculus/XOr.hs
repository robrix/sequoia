module Focalized.Calculus.XOr
( -- * Exclusive disjunction
  XOrIntro(..)
  -- * Connectives
, module Focalized.Connective.XOr
) where

import Focalized.Calculus.Context
import Focalized.Connective.XOr
import Focalized.Polarity

-- Exclusive disjunction

class XOrIntro s where
  xorL
    :: (Pos a, Pos b)
    => a < _Γ -|s r|- _Δ > b   ->   b < _Γ -|s r|- _Δ > a
    -- --------------------------------------------------
    ->             a </r/> b < _Γ -|s r|- _Δ

  xorR1
    :: (Pos a, Pos b)
    => _Γ -|s r|- _Δ > a   ->   b < _Γ -|s r|- _Δ
    -- ------------------------------------------
    ->         _Γ -|s r|- _Δ > a </r/> b

  xorR2
    :: (Pos a, Pos b)
    => _Γ -|s r|- _Δ > b   ->   a < _Γ -|s r|- _Δ
    -- ------------------------------------------
    ->         _Γ -|s r|- _Δ > a </r/> b
