{-# LANGUAGE QuantifiedConstraints #-}
module Focalized.Calculus.Mu
( -- * Recursion
  Recursion(..)
, muL'
  -- * Connectives
, module Focalized.Recursion
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Implication
import Focalized.Polarity
import Focalized.Quantification
import Focalized.Recursion
import Prelude hiding (init)

-- Recursion

class Recursion s where
  muL
    :: ((Neg ==> Pos) f, Neg a)
    => i -|s r|- o > f a ~~r~> a   ->   a < i -|s r|- o
    -- ------------------------------------------------
    ->              Mu r f < i -|s r|- o

  muR
    :: (Neg ==> Pos) f
    => i -|s r|- o > ForAll r N (MuF r f)
    -- ----------------------------------
    -> i -|s r|- o >             Mu  r f


muL'
  :: (Weaken s, Exchange s, Recursion s, (Neg ==> Pos) f)
  =>             Mu  r f  < i -|s r|- o
  -- ----------------------------------
  -> ForAll r N (MuF r f) < i -|s r|- o
muL' p = muR init >>> wkL' p
