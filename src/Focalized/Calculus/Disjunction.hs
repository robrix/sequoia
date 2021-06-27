module Focalized.Calculus.Disjunction
( -- * Multiplicative disjunction
  MultiplicativeDisj(..)
, parR'
  -- * Additive disjunction
, AdditiveDisj(..)
, sumL1'
, sumL2'
  -- * Connectives
, module Focalized.Disjunction
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Disjunction
import Focalized.Polarity
import Prelude hiding (init)

-- Multiplicative disjunction

class MultiplicativeDisj s where
  parL
    :: (Neg a, Neg b)
    => a < i -|s r|- o   ->   b < i -|s r|- o
    -- --------------------------------------
    ->          a ⅋ b < i -|s r|- o

  parR
    :: (Neg a, Neg b)
    => i -|s r|- o > a > b
    -- -------------------
    -> i -|s r|- o > a ⅋ b


parR'
  :: (Weaken s, Contextual s, MultiplicativeDisj s, Neg a, Neg b)
  => i -|s r|- o > a ⅋ b
  -- -------------------
  -> i -|s r|- o > a > b
parR' p = poppedR (wkR . wkR) p >>> parL (wkR init) init


-- Additive disjunction

class AdditiveDisj s where
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
  :: (Weaken s, Exchange s, AdditiveDisj s, Pos a, Pos b)
  => a ⊕ b < i -|s r|- o
  -- -------------------
  -> a     < i -|s r|- o
sumL1' p = sumR1 init >>> wkL' p

sumL2'
  :: (Weaken s, Exchange s, AdditiveDisj s, Pos a, Pos b)
  => a ⊕ b < i -|s r|- o
  -- -------------------
  ->     b < i -|s r|- o
sumL2' p = sumR2 init >>> wkL' p
