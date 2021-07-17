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

class Core s => OneIntro s where
  oneL
    ::       _Γ -|s e r|- _Δ
    -- ---------------------
    -> One < _Γ -|s e r|- _Δ

  oneR
    -- ---------------------
    :: _Γ -|s e r|- _Δ > One


oneL'
  :: OneIntro s
  => One < _Γ -|s e r|- _Δ
  -- ---------------------
  ->       _Γ -|s e r|- _Δ
oneL' = (oneR >>>)
