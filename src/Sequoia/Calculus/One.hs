module Sequoia.Calculus.One
( -- * One
  OneIntro(..)
, oneL'
  -- * Connctives
, module Sequoia.Connective.One
) where

import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Connective.One

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
