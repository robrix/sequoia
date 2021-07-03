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
import Focalized.Continuation
import Focalized.Polarity
import Prelude hiding (init)

-- Exclusive disjunction

class Core s => XOrIntro s where
  xorL
    :: (Pos a, Pos b)
    => a < _Γ -|s|- _Δ > b   ->   b < _Γ -|s|- _Δ > a
    -- ----------------------------------------------
    ->         a </R (K s)/> b < _Γ -|s|- _Δ

  xorR1
    :: (Pos a, Pos b)
    => _Γ -|s|- _Δ > a   ->   b < _Γ -|s|- _Δ
    -- --------------------------------------
    ->     _Γ -|s|- _Δ > a </R (K s)/> b

  xorR2
    :: (Pos a, Pos b)
    => _Γ -|s|- _Δ > b   ->   a < _Γ -|s|- _Δ
    -- --------------------------------------
    ->     _Γ -|s|- _Δ > a </R (K s)/> b

xorL1'
  :: (Weaken s, Exchange s, XOrIntro s, Pos a, Pos b)
  => a </R (K s)/> b < _Γ -|s|- _Δ
  -- ---------------------------------
  ->               a < _Γ -|s|- _Δ > b
xorL1' s = xorR1 init init >>> wkR (wkL' s)

xorL2'
  :: (Weaken s, Exchange s, XOrIntro s, Pos a, Pos b)
  => a </R (K s)/> b < _Γ -|s|- _Δ
  -- ---------------------------------
  ->               b < _Γ -|s|- _Δ > a
xorL2' s = xorR2 init init >>> wkR (wkL' s)
