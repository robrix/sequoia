module Focalized.Calculus.Iff
( -- * Logical biconditional
  IffIntro(..)
  -- * Connectives
, module Focalized.Connective.Iff
) where

import Focalized.Calculus.Context
import Focalized.Connective.Iff

-- * Logical biconditional

class IffIntro s where
  iffL1
    :: _Γ -|s r|- _Δ > a   ->   b < _Γ -|s r|- _Δ
    -- ------------------------------------------
    ->         a <~r~> b < _Γ -|s r|- _Δ

  iffL2
    :: _Γ -|s r|- _Δ > a   ->   b < _Γ -|s r|- _Δ
    -- ------------------------------------------
    ->         a <~r~> b < _Γ -|s r|- _Δ

  iffR
    :: a < _Γ -|s r|- _Δ > b   ->   b < _Γ -|s r|- _Δ > a
    -- --------------------------------------------------
    ->             _Γ -|s r|- _Δ > a <~r~> b
