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
import Sequoia.Calculus.Structural
import Sequoia.Connective.XOr
import Sequoia.Polarity

-- Exclusive disjunction

class Core s => XOrIntro s where
  xorL
    :: (Pos a, Pos b)
    => b < _Γ -|s e r|- _Δ > a   ->   a < _Γ -|s e r|- _Δ > b
    -- ------------------------------------------------------
    ->           a </XOr e r/> b < _Γ -|s e r|- _Δ

  xorR1
    :: (Pos a, Pos b)
    => _Γ -|s e r|- _Δ > b   ->   a < _Γ -|s e r|- _Δ
    -- ----------------------------------------------
    ->       _Γ -|s e r|- _Δ > a </XOr e r/> b

  xorR2
    :: (Pos a, Pos b)
    => _Γ -|s e r|- _Δ > a   ->   b < _Γ -|s e r|- _Δ
    -- ----------------------------------------------
    ->       _Γ -|s e r|- _Δ > a </XOr e r/> b

xorL1'
  :: (Weaken s, Exchange s, XOrIntro s, Pos a, Pos b)
  => a </XOr e r/> b < _Γ -|s e r|- _Δ
  -- -------------------------------------
  ->               b < _Γ -|s e r|- _Δ > a
xorL1' s = xorR1 init init >>> wkR (wkL' s)

xorL2'
  :: (Weaken s, Exchange s, XOrIntro s, Pos a, Pos b)
  => a </XOr e r/> b < _Γ -|s e r|- _Δ
  -- -------------------------------------
  ->               a < _Γ -|s e r|- _Δ > b
xorL2' s = xorR2 init init >>> wkR (wkL' s)
