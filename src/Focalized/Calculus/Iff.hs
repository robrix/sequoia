module Focalized.Calculus.Iff
( -- * Logical biconditional
  IffIntro(..)
, iffR1'
, iffR2'
  -- * Connectives
, module Focalized.Connective.Iff
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Connective.Iff
import Focalized.Polarity
import Prelude hiding (init)

-- * Logical biconditional

class IffIntro s where
  iffL1
    :: (Neg a, Neg b)
    => _Γ -|s r|- _Δ > a   ->   b < _Γ -|s r|- _Δ
    -- ------------------------------------------
    ->         a <~r~> b < _Γ -|s r|- _Δ

  iffL2
    :: (Neg a, Neg b)
    => _Γ -|s r|- _Δ > b   ->   a < _Γ -|s r|- _Δ
    -- ------------------------------------------
    ->         a <~r~> b < _Γ -|s r|- _Δ

  iffR
    :: (Neg a, Neg b)
    => a < _Γ -|s r|- _Δ > b   ->   b < _Γ -|s r|- _Δ > a
    -- --------------------------------------------------
    ->             _Γ -|s r|- _Δ > a <~r~> b


iffR1'
  :: (Weaken s, Exchange s, IffIntro s, Neg a, Neg b)
  =>     _Γ -|s r|- _Δ > a <~r~> b
  -- --------------------------------------------------
  -> a < _Γ -|s r|- _Δ > b
iffR1' s = wkL (wkR' s) >>> iffL1 init init

iffR2'
  :: (Weaken s, Exchange s, IffIntro s, Neg a, Neg b)
  =>     _Γ -|s r|- _Δ > a <~r~> b
  -- --------------------------------------------------
  -> b < _Γ -|s r|- _Δ > a
iffR2' s = wkL (wkR' s) >>> iffL2 init init
