module Focalized.Calculus.Top
( -- * Negative truth
  NegTruth(..)
  -- * Connctives
, module Focalized.Truth
) where

import Focalized.Calculus.Context
import Focalized.Truth

-- Negative truth

class NegTruth s where
  topR
    -- -----------------
    :: i -|s r|- o > Top
