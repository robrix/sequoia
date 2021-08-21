module Sequoia.Calculus.Iff
( -- * Logical biconditional
  IffIntro(..)
, iffR1'
, iffR2'
  -- * Connectives
, module Sequoia.Connective.Iff
) where

import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Calculus.Structural
import Sequoia.Connective.Iff
import Sequoia.Polarity

-- * Logical biconditional

class Core s => IffIntro s where
  iffL1
    :: (Neg a, Neg b)
    => _Γ ⊣s e r⊢ _Δ > a   ->   b < _Γ ⊣s e r⊢ _Δ
    -- ----------------------------------------------
    ->     a <~Iff e r~> b < _Γ ⊣s e r⊢ _Δ

  iffL2
    :: (Neg a, Neg b)
    => _Γ ⊣s e r⊢ _Δ > b   ->   a < _Γ ⊣s e r⊢ _Δ
    -- ----------------------------------------------
    ->     a <~Iff e r~> b < _Γ ⊣s e r⊢ _Δ

  iffR
    :: (Neg a, Neg b)
    => a < _Γ ⊣s e r⊢ _Δ > b   ->   b < _Γ ⊣s e r⊢ _Δ > a
    -- ------------------------------------------------------
    ->           _Γ ⊣s e r⊢ _Δ > a <~Iff e r~> b


iffR1'
  :: (Weaken s, Exchange s, IffIntro s, Neg a, Neg b)
  =>     _Γ ⊣s e r⊢ _Δ > a <~Iff e r~> b
  -- -------------------------------------
  -> a < _Γ ⊣s e r⊢ _Δ > b
iffR1' s = wkL (wkR' s) >>> iffL1 init init

iffR2'
  :: (Weaken s, Exchange s, IffIntro s, Neg a, Neg b)
  =>     _Γ ⊣s e r⊢ _Δ > a <~Iff e r~> b
  -- -------------------------------------
  -> b < _Γ ⊣s e r⊢ _Δ > a
iffR2' s = wkL (wkR' s) >>> iffL2 init init
