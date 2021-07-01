module Focalized.Calculus.Bottom
( -- * Bottom
  BottomIntro(..)
, botR'
  -- * Connectives
, module Focalized.Bottom
) where

import Focalized.Bottom
import Focalized.Calculus.Context
import Focalized.Calculus.Core

-- Bottom

class BottomIntro s where
  botL
    -- -------------------
    :: Bot < _Γ -|s r|- _Δ

  botR
    :: _Γ -|s r|- _Δ
    -- -------------------
    -> _Γ -|s r|- _Δ > Bot


botR'
  :: (Core s, BottomIntro s)
  => _Γ -|s r|- _Δ > Bot
  -- -------------------
  -> _Γ -|s r|- _Δ
botR' = (>>> botL)
