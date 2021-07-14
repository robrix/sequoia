module Sequoia.Calculus.Top
( -- * Top
  TopIntro(..)
  -- * Connctives
, module Sequoia.Connective.Top
) where

import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Connective.Top

-- Top

class Core k v s => TopIntro k v s where
  topR
    -- -----------------
    :: _Γ -|s|- _Δ > Top
