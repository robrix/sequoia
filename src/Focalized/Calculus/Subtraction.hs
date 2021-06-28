module Focalized.Calculus.Subtraction
( -- * Subtraction
  Subtraction(..)
, subL'
  -- * Connectives
, module Focalized.Implication
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Implication
import Focalized.Polarity
import Prelude hiding (init)

-- Subtraction

class Subtraction s where
  subL
    :: (Pos a, Neg b)
    =>         a < i -|s r|- o > b
    -- ---------------------------
    -> a ~-r-< b < i -|s r|- o

  subR
    :: (Pos a, Neg b)
    => i -|s r|- o > a   ->   b < i -|s r|- o
    -- --------------------------------------
    ->        i -|s r|- o > a ~-r-< b


subL'
  :: (Weaken s, Exchange s, Subtraction s, Pos a, Neg b)
  => a ~-r-< b < i -|s r|- o
  -- ---------------------------
  ->         a < i -|s r|- o > b
subL' p = subR init init >>> wkR (wkL' p)
