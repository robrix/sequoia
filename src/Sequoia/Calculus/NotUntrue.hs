module Sequoia.Calculus.NotUntrue
( -- * NotUntrue
  NotUntrueIntro(..)
  -- * Connectives
, module Sequoia.Connective.NotUntrue
) where

import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Connective.NotUntrue
import Sequoia.Polarity

-- NotUntrue

class Core s => NotUntrueIntro s where
  notUntrueL
    :: Neg a
    =>     a < _Γ ⊣s e r⊢ _Δ
    -- -----------------------
    -> e ≁ a < _Γ ⊣s e r⊢ _Δ

  notUntrueR
    :: Neg a
    => _Γ ⊣s e r⊢ _Δ > a
    -- -----------------------
    -> _Γ ⊣s e r⊢ _Δ > e ≁ a
