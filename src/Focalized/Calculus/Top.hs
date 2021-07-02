module Focalized.Calculus.Top
( -- * Top
  TopIntro(..)
  -- * Connctives
, module Focalized.Connective.Top
) where

import Focalized.Calculus.Context
import Focalized.Connective.Top

-- Top

class TopIntro s where
  topR
    -- -------------------
    :: _Γ -|s r|- _Δ > Top
