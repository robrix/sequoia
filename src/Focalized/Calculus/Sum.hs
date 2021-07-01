module Focalized.Calculus.Sum
( -- * Sum
  SumIntro(..)
, sumL1'
, sumL2'
  -- * Connectives
, module Focalized.Sum
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Polarity
import Focalized.Sum
import Prelude hiding (init)

-- Sum

class SumIntro s where
  sumL
    :: (Pos a, Pos b)
    => a < _Γ -|s r|- _Δ   ->   b < _Γ -|s r|- _Δ
    -- ------------------------------------------
    ->           a ⊕ b < _Γ -|s r|- _Δ

  sumR1
    :: (Pos a, Pos b)
    => _Γ -|s r|- _Δ > a
    -- ---------------------
    -> _Γ -|s r|- _Δ > a ⊕ b

  sumR2
    :: (Pos a, Pos b)
    => _Γ -|s r|- _Δ >     b
    -- ---------------------
    -> _Γ -|s r|- _Δ > a ⊕ b


sumL1'
  :: (Weaken s, Exchange s, SumIntro s, Pos a, Pos b)
  => a ⊕ b < _Γ -|s r|- _Δ
  -- ---------------------
  -> a     < _Γ -|s r|- _Δ
sumL1' p = sumR1 init >>> wkL' p

sumL2'
  :: (Weaken s, Exchange s, SumIntro s, Pos a, Pos b)
  => a ⊕ b < _Γ -|s r|- _Δ
  -- ---------------------
  ->     b < _Γ -|s r|- _Δ
sumL2' p = sumR2 init >>> wkL' p
