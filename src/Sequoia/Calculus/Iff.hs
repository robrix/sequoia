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
import Sequoia.Connective.Iff
import Sequoia.Polarity

-- * Logical biconditional

class Core r e s => IffIntro r e s where
  iffL1
    :: (Neg a, Neg b)
    => _Γ -|s|- _Δ > a   ->   b < _Γ -|s|- _Δ
    -- --------------------------------------
    ->     a <~Iff r e~> b < _Γ -|s|- _Δ

  iffL2
    :: (Neg a, Neg b)
    => _Γ -|s|- _Δ > b   ->   a < _Γ -|s|- _Δ
    -- --------------------------------------
    ->     a <~Iff r e~> b < _Γ -|s|- _Δ

  iffR
    :: (Neg a, Neg b)
    => a < _Γ -|s|- _Δ > b   ->   b < _Γ -|s|- _Δ > a
    -- ----------------------------------------------
    ->           _Γ -|s|- _Δ > a <~Iff r e~> b


iffR1'
  :: (Weaken r e s, Exchange r e s, IffIntro r e s, Neg a, Neg b)
  =>     _Γ -|s|- _Δ > a <~Iff r e~> b
  -- ---------------------------------
  -> a < _Γ -|s|- _Δ > b
iffR1' s = wkL (wkR' s) >>> iffL1 init init

iffR2'
  :: (Weaken r e s, Exchange r e s, IffIntro r e s, Neg a, Neg b)
  =>     _Γ -|s|- _Δ > a <~Iff r e~> b
  -- ---------------------------------
  -> b < _Γ -|s|- _Δ > a
iffR2' s = wkL (wkR' s) >>> iffL2 init init
