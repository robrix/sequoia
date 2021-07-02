module Focalized.Calculus.With
( -- * With
  WithIntro(..)
, withR1'
, withR2'
, withIdentityL
, withIdentityR
  -- * Connectives
, module Focalized.With
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Calculus.Top
import Focalized.Polarity
import Focalized.With
import Prelude hiding (init)

-- With

class WithIntro s where
  withL1
    :: (Neg a, Neg b)
    => a     < _Γ -|s r|- _Δ
    -- ---------------------
    -> a & b < _Γ -|s r|- _Δ

  withL2
    :: (Neg a, Neg b)
    =>     b < _Γ -|s r|- _Δ
    -- ---------------------
    -> a & b < _Γ -|s r|- _Δ

  withR, (⊢&)
    :: (Neg a, Neg b)
    => _Γ -|s r|- _Δ > a   ->   _Γ -|s r|- _Δ > b
    -- ------------------------------------------
    ->           _Γ -|s r|- _Δ > a & b
  (⊢&) = withR

  infixr 6 ⊢&


withR1'
  :: (Weaken s, Exchange s, WithIntro s, Neg a, Neg b)
  => _Γ -|s r|- _Δ > a & b
  -- ---------------------
  -> _Γ -|s r|- _Δ > a
withR1' t = wkR' t >>> withL1 init

withR2'
  :: (Weaken s, Exchange s, WithIntro s, Neg a, Neg b)
  => _Γ -|s r|- _Δ > a & b
  -- ---------------------
  -> _Γ -|s r|- _Δ > b
withR2' t = wkR' t >>> withL2 init


withIdentityL
  :: (Core s, WithIntro s, Neg a)
  -- ----------------------------
  => Top & a < _Γ -|s r|- _Δ > a
withIdentityL = withL2 init

withIdentityR
  :: (Core s, WithIntro s, TopIntro s, Neg a)
  -- ----------------------------
  => a < _Γ -|s r|- _Δ > a & Top
withIdentityR = init ⊢& topR

withAssociativity
  :: (Core s, WithIntro s, Neg a, Neg b, Neg c)
  -- -----------------------------------------
  => a & (b & c) < _Γ -|s r|- _Δ > (a & b) & c
withAssociativity = (withL1 init ⊢& withL2 (withL1 init)) ⊢& withL2 (withL2 init)
