module Focalized.Calculus.Top
( -- * Negative truth
  NegTruth(..)
  -- * Connctives
, module Focalized.Top
) where

import Focalized.Calculus.Context
import Focalized.Top

-- Negative truth

class NegTruth s where
  topR
    -- -------------------
    :: _Γ -|s r|- _Δ > Top
