module Focalized.Calculus.With
( -- * Negative conjunction
  NegConjunction(..)
, withR1'
, withR2'
  -- * Connectives
, module Focalized.With
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Polarity
import Focalized.With
import Prelude hiding (init)

-- Negative conjunction

class NegConjunction s where
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
  :: (Weaken s, Exchange s, NegConjunction s, Neg a, Neg b)
  => i -|s r|- o > a & b
  -- -------------------
  -> i -|s r|- o > a
withR1' t = wkR' t >>> withL1 init

withR2'
  :: (Weaken s, Exchange s, NegConjunction s, Neg a, Neg b)
  => i -|s r|- o > a & b
  -- -------------------
  -> i -|s r|- o > b
withR2' t = wkR' t >>> withL2 init
