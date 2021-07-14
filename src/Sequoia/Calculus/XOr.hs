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

class Core k v s => XOrIntro k v s where
  xorL
    :: (Pos a, Pos b)
    => a < _Γ -|s|- _Δ > b   ->   b < _Γ -|s|- _Δ > a
    -- ----------------------------------------------
    ->           a </k/> b < _Γ -|s|- _Δ

  xorR1
    :: (Pos a, Pos b)
    => _Γ -|s|- _Δ > a   ->   b < _Γ -|s|- _Δ
    -- --------------------------------------
    ->       _Γ -|s|- _Δ > a </k/> b

  xorR2
    :: (Pos a, Pos b)
    => _Γ -|s|- _Δ > b   ->   a < _Γ -|s|- _Δ
    -- --------------------------------------
    ->       _Γ -|s|- _Δ > a </k/> b

xorL1'
  :: (Weaken k v s, Exchange k v s, XOrIntro k v s, Pos a, Pos b)
  => a </k/> b < _Γ -|s|- _Δ
  -- ---------------------------
  ->         a < _Γ -|s|- _Δ > b
xorL1' s = xorR1 init init >>> wkR (wkL' s)

xorL2'
  :: (Weaken k v s, Exchange k v s, XOrIntro k v s, Pos a, Pos b)
  => a </k/> b < _Γ -|s|- _Δ
  -- ---------------------------
  ->         b < _Γ -|s|- _Δ > a
xorL2' s = xorR2 init init >>> wkR (wkL' s)
