module Focalized.Calculus.Zero
( -- * Additive falsity
  AdditiveFalsity(..)
  -- * Connectives
, module Focalized.Falsity
) where

import Focalized.Calculus.Context
import Focalized.Falsity

-- Additive falsity

class AdditiveFalsity s where
  zeroL
    -- ------------------
    :: Zero < i -|s r|- o
