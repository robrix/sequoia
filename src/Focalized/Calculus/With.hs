module Focalized.Calculus.With
( -- * With
  WithIntro(..)
, withR1'
, withR2'
  -- * Connectives
, module Focalized.With
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
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

  withR
    :: (Neg a, Neg b)
    => _Γ -|s r|- _Δ > a   ->   _Γ -|s r|- _Δ > b
    -- ------------------------------------------
    ->           _Γ -|s r|- _Δ > a & b


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
