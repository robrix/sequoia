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

class Core k v s => BottomIntro k v s where
  botL
    -- --------------------
    :: Bottom < _Γ -|s|- _Δ

  botR
    :: _Γ -|s|- _Δ
    -- --------------------
    -> _Γ -|s|- _Δ > Bottom


botR'
  :: BottomIntro k v s
  => _Γ -|s|- _Δ > Bottom
  -- --------------------
  -> _Γ -|s|- _Δ
botR' = (>>> botL)
