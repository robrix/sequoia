module Sequoia.Calculus.Bottom
( -- * Bottom
  BottomIntro(..)
, botR'
  -- * Connectives
, module Sequoia.Connective.Bottom
) where

import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Connective.Bottom

-- Bottom

class BottomIntro s where
  botL
    -- ------------------------
    :: Bottom < _Γ -|s e r|- _Δ

  botR
    :: _Γ -|s e r|- _Δ
    -- ------------------------
    -> _Γ -|s e r|- _Δ > Bottom


botR'
  :: (Core e r (s e r), BottomIntro s)
  => _Γ -|s e r|- _Δ > Bottom
  -- ------------------------
  -> _Γ -|s e r|- _Δ
botR' = (>>> botL)
