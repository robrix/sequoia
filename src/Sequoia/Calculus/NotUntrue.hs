module Sequoia.Calculus.NotUntrue
( -- * NotUntrue
  NotUntrueIntro(..)
  -- * Connectives
, module Sequoia.Connective.Assertion
) where

import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Connective.Assertion
import Sequoia.Polarity

-- NotUntrue

class Core s => NotUntrueIntro s where
  notUntrueL
    :: Neg a
    =>    a < _Γ -|s e r|- _Δ
    -- ----------------------
    -> r ≁a < _Γ -|s e r|- _Δ
