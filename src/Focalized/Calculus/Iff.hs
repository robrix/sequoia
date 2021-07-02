module Focalized.Calculus.Iff
( -- * Logical biconditional
  IffIntro(..)
  -- * Connectives
, module Focalized.Connective.Iff
) where

import Focalized.Calculus.Context
import Focalized.Connective.Iff
import Focalized.Polarity

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
