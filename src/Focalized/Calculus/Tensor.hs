module Focalized.Calculus.Tensor
( -- * Positive conjunction
  PosConjunction(..)
, tensorL'
  -- * Connectives
, module Focalized.Tensor
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Polarity
import Focalized.Tensor
import Prelude hiding (init)

-- Positive conjunction

class PosConjunction s where
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
  :: (Contextual s, Weaken s, PosConjunction s, Pos a, Pos b)
  => a ⊗ b < i -|s r|- o
  -- -------------------
  -> a < b < i -|s r|- o
tensorL' p = tensorR init (wkL init) >>> popL (wkL . wkL . pushL p)
