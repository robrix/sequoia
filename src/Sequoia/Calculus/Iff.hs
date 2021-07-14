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

class Core k v s => IffIntro k v s where
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
  :: (Weaken k v s, Exchange k v s, IffIntro k v s, Neg a, Neg b)
  =>     _Γ -|s|- _Δ > a <~k~> b
  -- ---------------------------
  -> a < _Γ -|s|- _Δ > b
iffR1' s = wkL (wkR' s) >>> iffL1 init init

iffR2'
  :: (Weaken k v s, Exchange k v s, IffIntro k v s, Neg a, Neg b)
  =>     _Γ -|s|- _Δ > a <~k~> b
  -- ---------------------------------
  -> b < _Γ -|s|- _Δ > a
iffR2' s = wkL (wkR' s) >>> iffL2 init init
