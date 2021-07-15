module Sequoia.Calculus.XOr
( -- * Exclusive disjunction
  XOrIntro(..)
, xorL1'
, xorL2'
  -- * Connectives
, module Sequoia.Connective.XOr
) where

import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Connective.XOr
import Sequoia.Polarity

-- Exclusive disjunction

class Core r e s => XOrIntro r e s where
  xorL
    :: (Pos a, Pos b)
    => a < _Γ -|s|- _Δ > b   ->   b < _Γ -|s|- _Δ > a
    -- ----------------------------------------------
    ->           a </r/> b < _Γ -|s|- _Δ

  xorR1
    :: (Pos a, Pos b)
    => _Γ -|s|- _Δ > a   ->   b < _Γ -|s|- _Δ
    -- --------------------------------------
    ->       _Γ -|s|- _Δ > a </r/> b

  xorR2
    :: (Pos a, Pos b)
    => _Γ -|s|- _Δ > b   ->   a < _Γ -|s|- _Δ
    -- --------------------------------------
    ->       _Γ -|s|- _Δ > a </r/> b

xorL1'
  :: (Weaken r e s, Exchange r e s, XOrIntro r e s, Pos a, Pos b)
  => a </r/> b < _Γ -|s|- _Δ
  -- ---------------------------
  ->         a < _Γ -|s|- _Δ > b
xorL1' s = xorR1 init init >>> wkR (wkL' s)

xorL2'
  :: (Weaken r e s, Exchange r e s, XOrIntro r e s, Pos a, Pos b)
  => a </r/> b < _Γ -|s|- _Δ
  -- ---------------------------
  ->         b < _Γ -|s|- _Δ > a
xorL2' s = xorR2 init init >>> wkR (wkL' s)
