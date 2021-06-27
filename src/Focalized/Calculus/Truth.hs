module Focalized.Calculus.Truth
( -- * Additive truth
  AdditiveTruth(..)
  -- * Multiplicative truth
, MultiplicativeTruth(..)
, oneL'
  -- * Connctives
, module Focalized.Truth
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Truth

-- Additive truth

class AdditiveTruth s where
  topR
    -- -----------------
    :: i -|s r|- o > Top


-- Multiplicative truth

class MultiplicativeTruth s where
  oneL
    :: i -|s r|- o
    -- -----------------
    -> One < i -|s r|- o

  oneR
    -- -----------------
    :: i -|s r|- o > One


oneL'
  :: (Core s, MultiplicativeTruth s)
  => One < i -|s r|- o
  -- -----------------
  -> i -|s r|- o
oneL' = (oneR >>>)
