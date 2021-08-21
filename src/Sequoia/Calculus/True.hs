module Sequoia.Calculus.True
( -- * True
  TrueIntro(..)
  -- * Connectives
, module Sequoia.Connective.True
) where

import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Connective.True
import Sequoia.Polarity

-- True

class Core s => TrueIntro s where
  trueL
    :: Pos a
    =>        a < _Γ ⊣s e r⊢ _Δ
    -- --------------------------
    -> True r a < _Γ ⊣s e r⊢ _Δ

  trueR
    :: Pos a
    => _Γ ⊣s e r⊢ _Δ > a
    -- --------------------------
    -> _Γ ⊣s e r⊢ _Δ > True r a
