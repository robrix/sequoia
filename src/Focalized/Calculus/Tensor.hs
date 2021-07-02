module Focalized.Calculus.Tensor
( -- * Tensor
  TensorIntro(..)
, tensorL'
, tensorIdentityL
, tensorIdentityR
, tensorAssociativity
, tensorCommutativity
, tensorDistributivity
, tensorAnnihilation
  -- * Connectives
, module Focalized.Tensor
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Calculus.One
import Focalized.Calculus.Sum
import Focalized.Calculus.Zero
import Focalized.Polarity
import Focalized.Tensor
import Prelude hiding (init)

-- Tensor

class TensorIntro s where
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
  :: (Contextual s, Weaken s, TensorIntro s, Pos a, Pos b)
  => a ⊗ b < _Γ -|s r|- _Δ
  -- ---------------------
  -> a < b < _Γ -|s r|- _Δ
tensorL' p = tensorR init (wkL init) >>> popL (wkL . wkL . pushL p)


tensorIdentityL
  :: (Core s, TensorIntro s, OneIntro s, Pos a)
  -- ---------------------------
  => One ⊗ a < _Γ -|s r|- _Δ > a
tensorIdentityL = tensorL (oneL init)

tensorIdentityR
  :: (Core s, TensorIntro s, OneIntro s, Pos a)
  -- ---------------------------
  => a < _Γ -|s r|- _Δ > a ⊗ One
tensorIdentityR = tensorR init oneR

tensorAssociativity
  :: (Weaken s, Exchange s, TensorIntro s, Pos a, Pos b, Pos c)
  -- -----------------------------------------
  => a ⊗ (b ⊗ c) < _Γ -|s r|- _Δ > (a ⊗ b) ⊗ c
tensorAssociativity = tensorL (exL (tensorL (tensorR (tensorR (wkL (exL init)) init) (exL init))))

tensorCommutativity
  :: (Exchange s, TensorIntro s, Pos a, Pos b)
  -- -----------------------------
  => a ⊗ b < _Γ -|s r|- _Δ > b ⊗ a
tensorCommutativity = tensorL (tensorR (exL init) init)

tensorDistributivity
  :: (Exchange s, TensorIntro s, SumIntro s, Pos a, Pos b, Pos c)
  -- -------------------------------------------
  => a ⊗ (b ⊕ c) < _Γ -|s r|- _Δ > a ⊗ b ⊕ a ⊗ c
tensorDistributivity = tensorL (exL (sumL (sumR1 (tensorR (exL init) init)) (sumR2 (tensorR (exL init) init))))

tensorAnnihilation
  :: (Exchange s, TensorIntro s, ZeroIntro s, Pos a)
  -- -----------------------------
  => a ⊗ Zero < _Γ -|s r|- _Δ
tensorAnnihilation = tensorL (exL zeroL)
