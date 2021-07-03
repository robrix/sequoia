module Focalized.Calculus.Iff
( -- * Logical biconditional
  IffIntro(..)
, iffR1'
, iffR2'
  -- * Connectives
, module Focalized.Connective.Iff
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Connective.Iff
import Focalized.Continuation
import Focalized.Polarity
import Prelude hiding (init)

-- * Logical biconditional

class IffIntro s where
  iffL1
    :: (Neg a, Neg b)
    => _Γ -|s|- _Δ > a   ->   b < _Γ -|s|- _Δ
    -- --------------------------------------
    ->     a <~R (K s)~> b < _Γ -|s|- _Δ

  iffL2
    :: (Neg a, Neg b)
    => _Γ -|s|- _Δ > b   ->   a < _Γ -|s|- _Δ
    -- --------------------------------------
    ->     a <~R (K s)~> b < _Γ -|s|- _Δ

  iffR
    :: (Neg a, Neg b)
    => a < _Γ -|s|- _Δ > b   ->   b < _Γ -|s|- _Δ > a
    -- ----------------------------------------------
    ->         _Γ -|s|- _Δ > a <~R (K s)~> b


iffR1'
  :: (Weaken s, Exchange s, IffIntro s, Neg a, Neg b)
  =>     _Γ -|s|- _Δ > a <~R (K s)~> b
  -- ---------------------------------
  -> a < _Γ -|s|- _Δ > b
iffR1' s = wkL (wkR' s) >>> iffL1 init init

iffR2'
  :: (Weaken s, Exchange s, IffIntro s, Neg a, Neg b)
  =>     _Γ -|s|- _Δ > a <~R (K s)~> b
  -- ---------------------------------
  -> b < _Γ -|s|- _Δ > a
iffR2' s = wkL (wkR' s) >>> iffL2 init init
