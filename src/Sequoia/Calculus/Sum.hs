module Sequoia.Calculus.Sum
( -- * Sum
  SumIntro(..)
, sumL1'
, sumL2'
, sumIdentityL
, sumIdentityR
, sumAssociativity
, sumCommutativity
  -- * Connectives
, module Sequoia.Connective.Sum
) where

import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Calculus.Structural
import Sequoia.Calculus.Zero
import Sequoia.Connective.Sum
import Sequoia.Polarity

-- Sum

class Core s => SumIntro s where
  sumL, (⊕⊢)
    :: (Pos a, Pos b)
    => a < _Γ ⊣s e r⊢ _Δ   ->   b < _Γ ⊣s e r⊢ _Δ
    -- ----------------------------------------------
    ->           a ⊕ b < _Γ ⊣s e r⊢ _Δ
  (⊕⊢) = sumL

  infixr 6 ⊕⊢

  sumR1
    :: (Pos a, Pos b)
    => _Γ ⊣s e r⊢ _Δ > a
    -- -----------------------
    -> _Γ ⊣s e r⊢ _Δ > a ⊕ b

  sumR2
    :: (Pos a, Pos b)
    => _Γ ⊣s e r⊢ _Δ >     b
    -- -----------------------
    -> _Γ ⊣s e r⊢ _Δ > a ⊕ b


sumL1'
  :: (Weaken s, Exchange s, SumIntro s, Pos a, Pos b)
  => a ⊕ b < _Γ ⊣s e r⊢ _Δ
  -- -----------------------
  -> a     < _Γ ⊣s e r⊢ _Δ
sumL1' p = sumR1 init >>> wkL' p

sumL2'
  :: (Weaken s, Exchange s, SumIntro s, Pos a, Pos b)
  => a ⊕ b < _Γ ⊣s e r⊢ _Δ
  -- -----------------------
  ->     b < _Γ ⊣s e r⊢ _Δ
sumL2' p = sumR2 init >>> wkL' p


sumIdentityL
  :: (SumIntro s, ZeroIntro s, Pos a)
  -- ----------------------------------
  => Zero ⊕ a < _Γ ⊣s e r⊢ _Δ > a
sumIdentityL = zeroL ⊕⊢ init

sumIdentityR
  :: (SumIntro s, Pos a)
  -- ------------------------------
  => a < _Γ ⊣s e r⊢ _Δ > a ⊕ Zero
sumIdentityR = sumR1 init

sumAssociativity
  :: (SumIntro s, Pos a, Pos b, Pos c)
  -- -------------------------------------------
  => a ⊕ (b ⊕ c) < _Γ ⊣s e r⊢ _Δ > (a ⊕ b) ⊕ c
sumAssociativity = sumR1 (sumR1 init) ⊕⊢ sumR1 (sumR2 init) ⊕⊢ sumR2 init

sumCommutativity
  :: (Exchange s, SumIntro s, Pos a, Pos b)
  -- -------------------------------
  => a ⊕ b < _Γ ⊣s e r⊢ _Δ > b ⊕ a
sumCommutativity = sumR2 init ⊕⊢ sumR1 init
