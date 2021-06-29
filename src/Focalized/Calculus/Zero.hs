module Focalized.Calculus.Zero
( -- * Positive falsity
  PosFalsity(..)
  -- * Connectives
, module Focalized.Zero
) where

import Focalized.Calculus.Context
import Focalized.Zero

-- Positive falsity

class PosFalsity s where
  zeroL
    -- ------------------
    :: Zero < _Γ -|s|- _Δ
