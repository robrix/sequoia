module Focalized.Calculus.Par
( -- * Negative disjunction
  NegDisjunction(..)
, parR'
  -- * Connectives
, module Focalized.Par
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Par
import Focalized.Polarity
import Prelude hiding (init)

-- Negative disjunction

class NegDisjunction s where
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
  :: (Weaken s, Contextual s, NegDisjunction s, Neg a, Neg b)
  => i -|s r|- o > a ⅋ b
  -- -------------------
  -> i -|s r|- o > a > b
parR' p = poppedR (wkR . wkR) p >>> parL (wkR init) init
