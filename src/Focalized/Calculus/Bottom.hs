module Focalized.Calculus.Bottom
( -- * Bottom
  BottomIntro(..)
, botR'
  -- * Connectives
, module Focalized.Connective.Bottom
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Connective.Bottom

-- Bottom

class Core s => BottomIntro s where
  botL
    -- --------------------
    :: Bottom < _Γ -|s|- _Δ

  botR
    :: _Γ -|s|- _Δ
    -- --------------------
    -> _Γ -|s|- _Δ > Bottom


botR'
  :: BottomIntro s
  => _Γ -|s|- _Δ > Bottom
  -- --------------------
  -> _Γ -|s|- _Δ
botR' = (>>> botL)
