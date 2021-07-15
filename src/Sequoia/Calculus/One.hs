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

class Core e r s => OneIntro e r s where
  oneL
    ::       _Γ -|s|- _Δ
    -- -----------------
    -> One < _Γ -|s|- _Δ

  oneR
    -- -----------------
    :: _Γ -|s|- _Δ > One


oneL'
  :: OneIntro e r s
  => One < _Γ -|s|- _Δ
  -- -----------------
  ->       _Γ -|s|- _Δ
oneL' = (oneR >>>)
