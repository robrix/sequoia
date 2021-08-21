module Sequoia.Calculus.Top
( -- * Top
  TopIntro(..)
  -- * Connctives
, module Sequoia.Connective.Top
) where

import Sequoia.Calculus.Context
import Sequoia.Connective.Top

-- Top

class TopIntro s where
  topR
    -- ---------------------
    :: _Γ ⊣s e r⊢ _Δ > Top
