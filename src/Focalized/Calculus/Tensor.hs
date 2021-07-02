module Focalized.Calculus.Tensor
( -- * Tensor
  TensorIntro(..)
, tensorL'
, tensorIdentityL
, tensorIdentityR
, tensorAssociativity
, tensorCommutativity
, tensorDistributivityL
, tensorDistributivityR
, tensorAnnihilationL
, tensorAnnihilationR
  -- * Connectives
, module Focalized.Connective.Tensor
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Calculus.One
import Focalized.Calculus.Sum
import Focalized.Calculus.Zero
import Focalized.Connective.Tensor
import Focalized.Polarity
import Prelude hiding (init)

-- Tensor

class TensorIntro s where
  tensorL
    :: (Pos a, Pos b)
    => a < b < _Γ -|s r|- _Δ
    -- ---------------------
    -> a ⊗ b < _Γ -|s r|- _Δ

  tensorR, (⊢⊗)
    :: (Pos a, Pos b)
    => _Γ -|s r|- _Δ > a   ->   _Γ -|s r|- _Δ > b
    -- ------------------------------------------
    ->           _Γ -|s r|- _Δ > a ⊗ b
  (⊢⊗) = tensorR

  infixr 7 ⊢⊗


tensorL'
  :: (Contextual s, Weaken s, TensorIntro s, Pos a, Pos b)
  => a ⊗ b < _Γ -|s r|- _Δ
  -- ---------------------
  -> a < b < _Γ -|s r|- _Δ
tensorL' p = init ⊢⊗ wkL init >>> popL (wkL . wkL . pushL p)


tensorIdentityL
  :: (Core s, TensorIntro s, OneIntro s, Pos a)
  -- ---------------------------
  => One ⊗ a < _Γ -|s r|- _Δ > a
tensorIdentityL = tensorL (oneL init)

tensorIdentityR
  :: (Core s, TensorIntro s, OneIntro s, Pos a)
  -- ---------------------------
  => a < _Γ -|s r|- _Δ > a ⊗ One
tensorIdentityR = init ⊢⊗ oneR

tensorAssociativity
  :: (Weaken s, Exchange s, TensorIntro s, Pos a, Pos b, Pos c)
  -- -----------------------------------------
  => a ⊗ (b ⊗ c) < _Γ -|s r|- _Δ > (a ⊗ b) ⊗ c
tensorAssociativity = tensorL (exL (tensorL ((wkL (exL init) ⊢⊗ init) ⊢⊗ exL init)))

tensorCommutativity
  :: (Exchange s, TensorIntro s, Pos a, Pos b)
  -- -----------------------------
  => a ⊗ b < _Γ -|s r|- _Δ > b ⊗ a
tensorCommutativity = tensorL (exL init ⊢⊗ init)

tensorDistributivityL
  :: (Exchange s, TensorIntro s, SumIntro s, Pos a, Pos b, Pos c)
  -- -------------------------------------------
  => a ⊗ c ⊕ b ⊗ c < _Γ -|s r|- _Δ > (a ⊕ b) ⊗ c
tensorDistributivityL = tensorL (sumR1 init ⊢⊗ exL init) ⊕⊢ tensorL (sumR2 init ⊢⊗ exL init)

tensorDistributivityR
  :: (Exchange s, TensorIntro s, SumIntro s, Pos a, Pos b, Pos c)
  -- -------------------------------------------
  => a ⊗ (b ⊕ c) < _Γ -|s r|- _Δ > a ⊗ b ⊕ a ⊗ c
tensorDistributivityR = tensorL (exL (sumR1 (exL init ⊢⊗ init) ⊕⊢ sumR2 (exL init ⊢⊗ init)))

tensorAnnihilationL
  :: (TensorIntro s, ZeroIntro s, Pos a)
  -- -----------------------------
  => Zero ⊗ a < _Γ -|s r|- _Δ > Zero
tensorAnnihilationL = tensorL zeroL

tensorAnnihilationR
  :: ZeroIntro s
  -- -----------------------------
  => Zero < _Γ -|s r|- _Δ > a ⊗ Zero
tensorAnnihilationR = zeroL
