module Sequoia.Calculus.Zero
( -- * Zero
  ZeroIntro(..)
  -- * Connectives
, module Sequoia.Connective.Zero
) where

import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Connective.Zero

-- Zero

class Core k s => ZeroIntro k s where
  zeroL
    -- ------------------
    :: Zero < _Γ -|s|- _Δ
