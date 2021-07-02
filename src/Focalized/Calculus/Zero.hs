module Focalized.Calculus.Zero
( -- * Zero
  ZeroIntro(..)
  -- * Connectives
, module Focalized.Connective.Zero
) where

import Focalized.Calculus.Context
import Focalized.Connective.Zero

-- Zero

class ZeroIntro s where
  zeroL
    -- --------------------
    :: Zero < _Γ -|s r|- _Δ
