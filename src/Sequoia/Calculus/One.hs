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

class OneIntro s where
  oneL
    ::       _Γ -|s e r|- _Δ
    -- ---------------------
    -> One < _Γ -|s e r|- _Δ

  oneR
    -- ---------------------
    :: _Γ -|s e r|- _Δ > One


oneL'
  :: (Core e r (s e r), OneIntro s)
  => One < _Γ -|s e r|- _Δ
  -- ---------------------
  ->       _Γ -|s e r|- _Δ
oneL' = (oneR >>>)
