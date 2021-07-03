module Focalized.Calculus.One
( -- * One
  OneIntro(..)
, oneL'
  -- * Connctives
, module Focalized.Connective.One
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Connective.One

-- One

class Core k s => OneIntro k s where
  oneL
    ::       _Γ -|s|- _Δ
    -- -----------------
    -> One < _Γ -|s|- _Δ

  oneR
    -- -----------------
    :: _Γ -|s|- _Δ > One


oneL'
  :: OneIntro k s
  => One < _Γ -|s|- _Δ
  -- -----------------
  ->       _Γ -|s|- _Δ
oneL' = (oneR >>>)
