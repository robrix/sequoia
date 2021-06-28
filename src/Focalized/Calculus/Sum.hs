module Focalized.Calculus.Sum
( -- * Positive disjunction
  PosDisjunction(..)
, sumL1'
, sumL2'
  -- * Connectives
, module Focalized.Sum
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Polarity
import Focalized.Sum
import Prelude hiding (init)

-- Positive disjunction

class PosDisjunction s where
  sumL
    :: (Pos a, Pos b)
    => a < i -|s r|- o   ->   b < i -|s r|- o
    -- --------------------------------------
    ->           a ⊕ b < i -|s r|- o

  sumR1
    :: (Pos a, Pos b)
    => i -|s r|- o > a
    -- -------------------
    -> i -|s r|- o > a ⊕ b

  sumR2
    :: (Pos a, Pos b)
    => i -|s r|- o >     b
    -- -------------------
    -> i -|s r|- o > a ⊕ b


sumL1'
  :: (Weaken s, Exchange s, PosDisjunction s, Pos a, Pos b)
  => a ⊕ b < i -|s r|- o
  -- -------------------
  -> a     < i -|s r|- o
sumL1' p = sumR1 init >>> wkL' p

sumL2'
  :: (Weaken s, Exchange s, PosDisjunction s, Pos a, Pos b)
  => a ⊕ b < i -|s r|- o
  -- -------------------
  ->     b < i -|s r|- o
sumL2' p = sumR2 init >>> wkL' p
