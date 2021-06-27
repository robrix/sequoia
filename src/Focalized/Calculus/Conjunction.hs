module Focalized.Calculus.Conjunction
( -- * Additive conjunction
  AdditiveConj(..)
, withR1'
, withR2'
  -- * Multiplicative conjunction
, MultiplicativeConj(..)
, tensorL'
  -- * Connectives
, module Focalized.Conjunction
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Conjunction
import Focalized.Polarity
import Prelude hiding (init)

-- Additive conjunction

class AdditiveConj s where
  withL1
    :: (Neg a, Neg b)
    => a     < i -|s r|- o
    -- -------------------
    -> a & b < i -|s r|- o
  withL2
    :: (Neg a, Neg b)
    =>     b < i -|s r|- o
    -- -------------------
    -> a & b < i -|s r|- o

  withR
    :: (Neg a, Neg b)
    => i -|s r|- o > a   ->   i -|s r|- o > b
    -- --------------------------------------
    ->           i -|s r|- o > a & b


withR1'
  :: (Weaken s, Exchange s, AdditiveConj s, Neg a, Neg b)
  => i -|s r|- o > a & b
  -- -------------------
  -> i -|s r|- o > a
withR1' t = wkR' t >>> withL1 init

withR2'
  :: (Weaken s, Exchange s, AdditiveConj s, Neg a, Neg b)
  => i -|s r|- o > a & b
  -- -------------------
  -> i -|s r|- o > b
withR2' t = wkR' t >>> withL2 init


-- Multiplicative conjunction

class MultiplicativeConj s where
  tensorL
    :: (Pos a, Pos b)
    => a < b < i -|s r|- o
    -- -------------------
    -> a ⊗ b < i -|s r|- o
  tensorR
    :: (Pos a, Pos b)
    => i -|s r|- o > a   ->   i -|s r|- o > b
    -- --------------------------------------
    ->          i -|s r|- o > a ⊗ b


tensorL'
  :: (Contextual s, Weaken s, MultiplicativeConj s, Pos a, Pos b)
  => a ⊗ b < i -|s r|- o
  -- -------------------
  -> a < b < i -|s r|- o
tensorL' p = tensorR init (wkL init) >>> popL (wkL . wkL . pushL p)
