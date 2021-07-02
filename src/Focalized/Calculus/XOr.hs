module Focalized.Calculus.XOr
( -- * Exclusive disjunction
  XOrIntro(..)
  -- * Connectives
, module Focalized.Connective.XOr
) where

import Focalized.Calculus.Context
import Focalized.Connective.XOr

-- Exclusive disjunction

class XOrIntro s where
  xorL
    :: a < _Γ -|s r|- _Δ > b   ->   b < _Γ -|s r|- _Δ > a
    -- --------------------------------------------------
    ->             a </r/> b < _Γ -|s r|- _Δ

  xorR1
    :: _Γ -|s r|- _Δ > a   ->   b < _Γ -|s r|- _Δ
    -- ------------------------------------------
    ->         _Γ -|s r|- _Δ > a </r/> b

  xorR2
    :: _Γ -|s r|- _Δ > b   ->   a < _Γ -|s r|- _Δ
    -- ------------------------------------------
    ->         _Γ -|s r|- _Δ > a </r/> b
