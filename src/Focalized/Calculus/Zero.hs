module Focalized.Calculus.Zero
( -- * Zero
  ZeroIntro(..)
  -- * Connectives
, module Focalized.Connective.Zero
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Connective.Zero

-- Zero

class Core s => ZeroIntro s where
  zeroL
    -- ------------------
    :: Zero < _Γ -|s|- _Δ
