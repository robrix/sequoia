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
    -- -----------------
    :: Bot < i -|s r|- o

  botR
    :: i -|s r|- o
    -- -----------------
    -> i -|s r|- o > Bot


botR'
  :: (Core s, NegFalsity s)
  => i -|s r|- o > Bot
  -- -----------------
  -> i -|s r|- o
botR' = (>>> botL)
