module Focalized.Calculus.Zero
( -- * Positive falsity
  PosFalsity(..)
  -- * Connectives
, module Focalized.Falsity
) where

import Focalized.Calculus.Context
import Focalized.Falsity

-- Positive falsity

class PosFalsity s where
  zeroL
    -- ------------------
    :: Zero < i -|s r|- o
