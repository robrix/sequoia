module Sequoia.Calculus.Tensor
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
, module Sequoia.Connective.Tensor
) where

import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Calculus.One
import Sequoia.Calculus.Structural
import Sequoia.Calculus.Sum
import Sequoia.Calculus.Zero
import Sequoia.Connective.Tensor
import Sequoia.Contextual
import Sequoia.Polarity

-- Tensor

class Core e r s => TensorIntro e r s where
  tensorL
    :: (Pos a, Pos b)
    => a < b < _Γ -|s|- _Δ
    -- -------------------
    -> a ⊗ b < _Γ -|s|- _Δ

  tensorR, (⊢⊗)
    :: (Pos a, Pos b)
    => _Γ -|s|- _Δ > a   ->   _Γ -|s|- _Δ > b
    -- --------------------------------------
    ->           _Γ -|s|- _Δ > a ⊗ b
  (⊢⊗) = tensorR

  infixr 7 ⊢⊗


tensorL'
  :: (Contextual e r s, Weaken e r s, TensorIntro e r s, Pos a, Pos b)
  => a ⊗ b < _Γ -|s|- _Δ
  -- -------------------
  -> a < b < _Γ -|s|- _Δ
tensorL' p = init ⊢⊗ wkL init >>> popL (wkL . wkL . pushL p)


tensorIdentityL
  :: (TensorIntro e r (s e r), OneIntro s, Pos a)
  -- -----------------------------
  => One ⊗ a < _Γ -|s e r|- _Δ > a
tensorIdentityL = tensorL (oneL init)

tensorIdentityR
  :: (TensorIntro e r (s e r), OneIntro s, Pos a)
  -- -----------------------------
  => a < _Γ -|s e r|- _Δ > a ⊗ One
tensorIdentityR = init ⊢⊗ oneR

tensorAssociativity
  :: (Weaken e r s, Exchange e r s, TensorIntro e r s, Pos a, Pos b, Pos c)
  -- ---------------------------------------
  => a ⊗ (b ⊗ c) < _Γ -|s|- _Δ > (a ⊗ b) ⊗ c
tensorAssociativity = tensorL (exL (tensorL ((wkL (exL init) ⊢⊗ init) ⊢⊗ exL init)))

tensorCommutativity
  :: (Exchange e r s, TensorIntro e r s, Pos a, Pos b)
  -- ---------------------------
  => a ⊗ b < _Γ -|s|- _Δ > b ⊗ a
tensorCommutativity = tensorL (exL init ⊢⊗ init)

tensorDistributivityL
  :: (Exchange e r s, TensorIntro e r s, SumIntro e r s, Pos a, Pos b, Pos c)
  -- -----------------------------------------
  => a ⊗ c ⊕ b ⊗ c < _Γ -|s|- _Δ > (a ⊕ b) ⊗ c
tensorDistributivityL = tensorL (sumR1 init ⊢⊗ exL init) ⊕⊢ tensorL (sumR2 init ⊢⊗ exL init)

tensorDistributivityR
  :: (Exchange e r s, TensorIntro e r s, SumIntro e r s, Pos a, Pos b, Pos c)
  -- -----------------------------------------
  => a ⊗ (b ⊕ c) < _Γ -|s|- _Δ > a ⊗ b ⊕ a ⊗ c
tensorDistributivityR = tensorL (exL (sumR1 (exL init ⊢⊗ init) ⊕⊢ sumR2 (exL init ⊢⊗ init)))

tensorAnnihilationL
  :: (TensorIntro e r s, ZeroIntro e r s, Pos a)
  -- -----------------------------
  => Zero ⊗ a < _Γ -|s|- _Δ > Zero
tensorAnnihilationL = tensorL zeroL

tensorAnnihilationR
  :: ZeroIntro e r s
  -- -----------------------------
  => Zero < _Γ -|s|- _Δ > a ⊗ Zero
tensorAnnihilationR = zeroL
