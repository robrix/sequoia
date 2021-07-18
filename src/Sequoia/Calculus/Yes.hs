module Sequoia.Calculus.Yes
( -- * Yes
  YesIntro(..)
  -- * Connectives
, module Sequoia.Connective.Assertion
) where

import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Connective.Assertion (Yes(..))
import Sequoia.Polarity

-- Yes

class Core s => YesIntro s where
  yesL
    :: Pos a
    =>       a < _Γ -|s e r|- _Δ
    -- -------------------------
    -> Yes e a < _Γ -|s e r|- _Δ
