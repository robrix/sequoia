module Focalized.Calculus.Top
( -- * Top
  TopIntro(..)
  -- * Connctives
, module Focalized.Connective.Top
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Connective.Top

-- Top

class Core s => TopIntro s where
  topR
    -- -----------------
    :: _Γ -|s|- _Δ > Top
