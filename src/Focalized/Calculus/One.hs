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

class OneIntro s where
  oneL
    ::       _Γ -|s r|- _Δ
    -- -------------------
    -> One < _Γ -|s r|- _Δ

  oneR
    -- -------------------
    :: _Γ -|s r|- _Δ > One


oneL'
  :: (Core s, OneIntro s)
  => One < _Γ -|s r|- _Δ
  -- -------------------
  ->       _Γ -|s r|- _Δ
oneL' = (oneR >>>)
