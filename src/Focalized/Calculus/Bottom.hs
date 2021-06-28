module Focalized.Calculus.Bottom
( -- * Multiplicative falsity
  MultiplicativeFalsity(..)
, botR'
  -- * Connectives
, module Focalized.Falsity
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Falsity

-- Multiplicative falsity

class MultiplicativeFalsity s where
  botL
    -- -----------------
    :: Bot < i -|s r|- o

  botR
    :: i -|s r|- o
    -- -----------------
    -> i -|s r|- o > Bot


botR'
  :: (Core s, MultiplicativeFalsity s)
  => i -|s r|- o > Bot
  -- -----------------
  -> i -|s r|- o
botR' = (>>> botL)
