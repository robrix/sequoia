module Sequoia.Calculus.Iff
( -- * Logical biconditional
  IffIntro(..)
, iffR1'
, iffR2'
  -- * Connectives
, module Sequoia.Connective.Iff
) where

import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Connective.Iff
import Sequoia.Polarity
import Prelude hiding (init)

-- * Logical biconditional

class Core k s => IffIntro k s where
  iffL1
    :: (Neg a, Neg b)
    => _Γ -|s|- _Δ > a   ->   b < _Γ -|s|- _Δ
    -- --------------------------------------
    ->     a <~k~> b < _Γ -|s|- _Δ

  iffL2
    :: (Neg a, Neg b)
    => _Γ -|s|- _Δ > b   ->   a < _Γ -|s|- _Δ
    -- --------------------------------------
    ->     a <~k~> b < _Γ -|s|- _Δ

  iffR
    :: (Neg a, Neg b)
    => a < _Γ -|s|- _Δ > b   ->   b < _Γ -|s|- _Δ > a
    -- ----------------------------------------------
    ->           _Γ -|s|- _Δ > a <~k~> b


iffR1'
  :: (Weaken k s, Exchange k s, IffIntro k s, Neg a, Neg b)
  =>     _Γ -|s|- _Δ > a <~k~> b
  -- ---------------------------
  -> a < _Γ -|s|- _Δ > b
iffR1' s = wkL (wkR' s) >>> iffL1 init init

iffR2'
  :: (Weaken k s, Exchange k s, IffIntro k s, Neg a, Neg b)
  =>     _Γ -|s|- _Δ > a <~k~> b
  -- ---------------------------------
  -> b < _Γ -|s|- _Δ > a
iffR2' s = wkL (wkR' s) >>> iffL2 init init
