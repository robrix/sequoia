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

class BottomIntro s where
  botL
    -- ----------------------
    :: Bottom < _Γ -|s r|- _Δ

  botR
    :: _Γ -|s r|- _Δ
    -- ----------------------
    -> _Γ -|s r|- _Δ > Bottom


botR'
  :: (Core s, BottomIntro s)
  => _Γ -|s r|- _Δ > Bottom
  -- ----------------------
  -> _Γ -|s r|- _Δ
botR' = (>>> botL)
