module Focalized.Calculus.Tensor
( -- * Positive conjunction
  PosConjunction(..)
, tensorL'
  -- * Connectives
, module Focalized.Tensor
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Polarity
import Focalized.Tensor
import Prelude hiding (init)

-- Positive conjunction

class PosConjunction s where
  tensorL
    :: (Pos a, Pos b)
    => a < b < _Γ -|s r|- _Δ
    -- ---------------------
    -> a ⊗ b < _Γ -|s r|- _Δ

  tensorR
    :: (Pos a, Pos b)
    => _Γ -|s r|- _Δ > a   ->   _Γ -|s r|- _Δ > b
    -- ------------------------------------------
    ->           _Γ -|s r|- _Δ > a ⊗ b


tensorL'
  :: (Contextual s, Weaken s, PosConjunction s, Pos a, Pos b)
  => a ⊗ b < _Γ -|s r|- _Δ
  -- ---------------------
  -> a < b < _Γ -|s r|- _Δ
tensorL' p = tensorR init (wkL init) >>> popL (wkL . wkL . pushL p)
