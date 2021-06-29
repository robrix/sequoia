module Focalized.Calculus.One
( -- * Positive truth
  PosTruth(..)
, oneL'
  -- * Connctives
, module Focalized.One
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.One

-- Positive truth

class PosTruth s where
  oneL
    :: _Γ -|s|- _Δ
    -- -----------------
    -> One < _Γ -|s|- _Δ

  oneR
    -- -----------------
    :: _Γ -|s|- _Δ > One


oneL'
  :: (Core s, PosTruth s)
  => One < _Γ -|s|- _Δ
  -- -----------------
  -> _Γ -|s|- _Δ
oneL' = (oneR >>>)
