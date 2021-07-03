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

class Core k s => TensorIntro k s where
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
  :: (Contextual k s, Weaken k s, TensorIntro k s, Pos a, Pos b)
  => a ⊗ b < _Γ -|s|- _Δ
  -- -------------------
  -> a < b < _Γ -|s|- _Δ
tensorL' p = init ⊢⊗ wkL init >>> popL (wkL . wkL . pushL p)


tensorIdentityL
  :: (TensorIntro k s, OneIntro k s, Pos a)
  -- -------------------------
  => One ⊗ a < _Γ -|s|- _Δ > a
tensorIdentityL = tensorL (oneL init)

tensorIdentityR
  :: (TensorIntro k s, OneIntro k s, Pos a)
  -- -------------------------
  => a < _Γ -|s|- _Δ > a ⊗ One
tensorIdentityR = init ⊢⊗ oneR

tensorAssociativity
  :: (Weaken k s, Exchange k s, TensorIntro k s, Pos a, Pos b, Pos c)
  -- ---------------------------------------
  => a ⊗ (b ⊗ c) < _Γ -|s|- _Δ > (a ⊗ b) ⊗ c
tensorAssociativity = tensorL (exL (tensorL ((wkL (exL init) ⊢⊗ init) ⊢⊗ exL init)))

tensorCommutativity
  :: (Exchange k s, TensorIntro k s, Pos a, Pos b)
  -- ---------------------------
  => a ⊗ b < _Γ -|s|- _Δ > b ⊗ a
tensorCommutativity = tensorL (exL init ⊢⊗ init)

tensorDistributivityL
  :: (Exchange k s, TensorIntro k s, SumIntro k s, Pos a, Pos b, Pos c)
  -- -----------------------------------------
  => a ⊗ c ⊕ b ⊗ c < _Γ -|s|- _Δ > (a ⊕ b) ⊗ c
tensorDistributivityL = tensorL (sumR1 init ⊢⊗ exL init) ⊕⊢ tensorL (sumR2 init ⊢⊗ exL init)

tensorDistributivityR
  :: (Exchange k s, TensorIntro k s, SumIntro k s, Pos a, Pos b, Pos c)
  -- -----------------------------------------
  => a ⊗ (b ⊕ c) < _Γ -|s|- _Δ > a ⊗ b ⊕ a ⊗ c
tensorDistributivityR = tensorL (exL (sumR1 (exL init ⊢⊗ init) ⊕⊢ sumR2 (exL init ⊢⊗ init)))

tensorAnnihilationL
  :: (TensorIntro k s, ZeroIntro k s, Pos a)
  -- -----------------------------
  => Zero ⊗ a < _Γ -|s|- _Δ > Zero
tensorAnnihilationL = tensorL zeroL

tensorAnnihilationR
  :: ZeroIntro k s
  -- -----------------------------
  => Zero < _Γ -|s|- _Δ > a ⊗ Zero
tensorAnnihilationR = zeroL
