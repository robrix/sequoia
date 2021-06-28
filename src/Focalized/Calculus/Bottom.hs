module Focalized.Calculus.Bottom
( -- * Negative falsity
  NegFalsity(..)
, botR'
  -- * Connectives
, module Focalized.Bottom
) where

import Focalized.Bottom
import Focalized.Calculus.Context
import Focalized.Calculus.Core

-- Negative falsity

class NegFalsity s where
  botL
    -- -------------------
    :: Bot < _Γ -|s r|- _Δ

  botR
    :: _Γ -|s r|- _Δ
    -- -------------------
    -> _Γ -|s r|- _Δ > Bot


botR'
  :: (Core s, NegFalsity s)
  => _Γ -|s r|- _Δ > Bot
  -- -------------------
  -> _Γ -|s r|- _Δ
botR' = (>>> botL)
