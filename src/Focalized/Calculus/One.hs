module Focalized.Calculus.One
( -- * Positive truth
  PosTruth(..)
, oneL'
  -- * Connctives
, module Focalized.Truth
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Truth

-- Positive truth

class PosTruth s where
  oneL
    :: i -|s r|- o
    -- -----------------
    -> One < i -|s r|- o

  oneR
    -- -----------------
    :: i -|s r|- o > One


oneL'
  :: (Core s, PosTruth s)
  => One < i -|s r|- o
  -- -----------------
  -> i -|s r|- o
oneL' = (oneR >>>)
