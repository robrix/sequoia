module Focalized.Calculus.Falsity
( -- * Multiplicative falsity
  MultiplicativeFalsity(..)
, botR'
  -- * Additive falsity
, AdditiveFalsity(..)
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


-- Additive falsity

class AdditiveFalsity s where
  zeroL
    -- ------------------
    :: Zero < i -|s r|- o
