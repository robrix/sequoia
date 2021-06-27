module Focalized.Calculus.Implication
( -- * Implication
  Implication(..)
, funL2
, ($$)
, funR'
  -- * Subtraction
, Subtraction(..)
, subL'
  -- * Connectives
, module Focalized.Implication
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Implication
import Focalized.Polarity
import Prelude hiding (init)

-- Implication

class Implication s where
  funL
    :: (Pos a, Neg b)
    => i -|s r|- o > a   ->   b < i -|s r|- o
    -- --------------------------------------
    ->        a ~~r~> b < i -|s r|- o

  funR
    :: (Pos a, Neg b)
    => a < i -|s r|- o > b
    -- ---------------------------
    ->     i -|s r|- o > a ~~r~> b


funL2
  :: (Core s, Implication s, Pos a, Neg b)
  -- -------------------------------
  => a ~~r~> b < a < i -|s r|- o > b
funL2 = funL init init

($$)
  :: (Weaken s, Exchange s, Implication s, Pos a, Neg b)
  => i -|s r|- o > a ~~r~> b   ->   i -|s r|- o > a
  -- ----------------------------------------------
  ->                i -|s r|- o > b
f $$ a = wkR' f >>> wkR' a `funL` init

funR'
  :: (Weaken s, Exchange s, Implication s, Pos a, Neg b)
  =>     i -|s r|- o > a ~~r~> b
  -- ---------------------------
  -> a < i -|s r|- o > b
funR' p = wkL (wkR' p) >>> funL2


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
