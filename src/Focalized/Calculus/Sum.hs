module Focalized.Calculus.Sum
( -- * Sum
  SumIntro(..)
, sumL1'
, sumL2'
, sumIdentityL
, sumIdentityR
  -- * Connectives
, module Focalized.Sum
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Calculus.Zero
import Focalized.Polarity
import Focalized.Sum
import Prelude hiding (init)

-- Sum

class SumIntro s where
  sumL, (⊕⊢)
    :: (Pos a, Pos b)
    => a < _Γ -|s r|- _Δ   ->   b < _Γ -|s r|- _Δ
    -- ------------------------------------------
    ->           a ⊕ b < _Γ -|s r|- _Δ
  (⊕⊢) = sumL

  infixr 6 ⊕⊢

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


sumIdentityL
  :: (Core s, SumIntro s, ZeroIntro s, Pos a)
  -- ----------------------------
  => Zero ⊕ a < _Γ -|s r|- _Δ > a
sumIdentityL = zeroL ⊕⊢ init

sumIdentityR
  :: (Core s, SumIntro s, Pos a)
  -- ----------------------------
  => a < _Γ -|s r|- _Δ > a ⊕ Zero
sumIdentityR = sumR1 init
