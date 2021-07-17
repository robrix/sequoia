module Sequoia.Calculus.Zero
( -- * Zero
  ZeroIntro(..)
  -- * Connectives
, module Sequoia.Connective.Zero
) where

import Sequoia.Calculus.Context
import Sequoia.Connective.Zero

-- Zero

class ZeroIntro s where
  zeroL
    -- ----------------------
    :: Zero < _Γ -|s e r|- _Δ
