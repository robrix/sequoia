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

class Core k v s => OneIntro k v s where
  oneL
    ::       _Γ -|s|- _Δ
    -- -----------------
    -> One < _Γ -|s|- _Δ

  oneR
    -- -----------------
    :: _Γ -|s|- _Δ > One


oneL'
  :: OneIntro k v s
  => One < _Γ -|s|- _Δ
  -- -----------------
  ->       _Γ -|s|- _Δ
oneL' = (oneR >>>)
