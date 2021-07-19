module Sequoia.Calculus.True
( -- * True
  TrueIntro(..)
  -- * Connectives
, module Sequoia.Connective.Assertion
) where

import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Connective.Assertion (True(..))
import Sequoia.Polarity

-- True

class Core s => TrueIntro s where
  trueL
    :: Pos a
    =>        a < _Γ -|s e r|- _Δ
    -- --------------------------
    -> True e a < _Γ -|s e r|- _Δ

  trueR
    :: Pos a
    => _Γ -|s e r|- _Δ > a
    -- --------------------------
    -> _Γ -|s e r|- _Δ > True e a
