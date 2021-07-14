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
import Sequoia.Calculus.Sum
import Sequoia.Calculus.Zero
import Sequoia.Connective.Tensor
import Sequoia.Polarity

-- Tensor

class Core k v s => TensorIntro k v s where
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
  :: (Contextual k v s, Weaken k v s, TensorIntro k v s, Pos a, Pos b)
  => a ⊗ b < _Γ -|s|- _Δ
  -- -------------------
  -> a < b < _Γ -|s|- _Δ
tensorL' p = init ⊢⊗ wkL init >>> popL (wkL . wkL . pushL p)


tensorIdentityL
  :: (TensorIntro k v s, OneIntro k v s, Pos a)
  -- -------------------------
  => One ⊗ a < _Γ -|s|- _Δ > a
tensorIdentityL = tensorL (oneL init)

tensorIdentityR
  :: (TensorIntro k v s, OneIntro k v s, Pos a)
  -- -------------------------
  => a < _Γ -|s|- _Δ > a ⊗ One
tensorIdentityR = init ⊢⊗ oneR

tensorAssociativity
  :: (Weaken k v s, Exchange k v s, TensorIntro k v s, Pos a, Pos b, Pos c)
  -- ---------------------------------------
  => a ⊗ (b ⊗ c) < _Γ -|s|- _Δ > (a ⊗ b) ⊗ c
tensorAssociativity = tensorL (exL (tensorL ((wkL (exL init) ⊢⊗ init) ⊢⊗ exL init)))

tensorCommutativity
  :: (Exchange k v s, TensorIntro k v s, Pos a, Pos b)
  -- ---------------------------
  => a ⊗ b < _Γ -|s|- _Δ > b ⊗ a
tensorCommutativity = tensorL (exL init ⊢⊗ init)

tensorDistributivityL
  :: (Exchange k v s, TensorIntro k v s, SumIntro k v s, Pos a, Pos b, Pos c)
  -- -----------------------------------------
  => a ⊗ c ⊕ b ⊗ c < _Γ -|s|- _Δ > (a ⊕ b) ⊗ c
tensorDistributivityL = tensorL (sumR1 init ⊢⊗ exL init) ⊕⊢ tensorL (sumR2 init ⊢⊗ exL init)

tensorDistributivityR
  :: (Exchange k v s, TensorIntro k v s, SumIntro k v s, Pos a, Pos b, Pos c)
  -- -----------------------------------------
  => a ⊗ (b ⊕ c) < _Γ -|s|- _Δ > a ⊗ b ⊕ a ⊗ c
tensorDistributivityR = tensorL (exL (sumR1 (exL init ⊢⊗ init) ⊕⊢ sumR2 (exL init ⊢⊗ init)))

tensorAnnihilationL
  :: (TensorIntro k v s, ZeroIntro k v s, Pos a)
  -- -----------------------------
  => Zero ⊗ a < _Γ -|s|- _Δ > Zero
tensorAnnihilationL = tensorL zeroL

tensorAnnihilationR
  :: ZeroIntro k v s
  -- -----------------------------
  => Zero < _Γ -|s|- _Δ > a ⊗ Zero
tensorAnnihilationR = zeroL
