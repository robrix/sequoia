module Focalized.Calculus.XOr
( -- * Exclusive disjunction
  XOrIntro(..)
, xorL1'
, xorL2'
  -- * Connectives
, module Focalized.Connective.XOr
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Connective.XOr
import Focalized.Polarity
import Prelude hiding (init)

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

xorL1'
  :: (Weaken s, Exchange s, XOrIntro s, Pos a, Pos b)
  => a </r/> b < _Γ -|s r|- _Δ
  -- -----------------------------
  ->         a < _Γ -|s r|- _Δ > b
xorL1' s = xorR1 init init >>> wkR (wkL' s)

xorL2'
  :: (Weaken s, Exchange s, XOrIntro s, Pos a, Pos b)
  => a </r/> b < _Γ -|s r|- _Δ
  -- -----------------------------
  ->         b < _Γ -|s r|- _Δ > a
xorL2' s = xorR2 init init >>> wkR (wkL' s)
