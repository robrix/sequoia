{-# LANGUAGE QuantifiedConstraints #-}
module Focalized.Calculus.Nu
( -- * Corecursion
  Corecursion(..)
, nuR'
  -- * Connectives
, module Focalized.Nu
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Nu
import Focalized.Polarity
import Focalized.Quantification
import Prelude hiding (init)

-- Corecursion

class Corecursion s where
  nuL
    :: (Pos ==> Neg) f
    => Exists r P (NuF r f) < i -|s r|- o
    -- ----------------------------------
    ->             Nu  r f  < i -|s r|- o

  nuR
    :: (Pos ==> Neg) f
    => i -|s r|- o > Exists r P (NuF r f)
    -- ----------------------------------
    -> i -|s r|- o >             Nu  r f


nuR'
  :: (Weaken s, Exchange s, Corecursion s, (Pos ==> Neg) f)
  => i -|s r|- o >             Nu  r f
  -- ----------------------------------
  -> i -|s r|- o > Exists r P (NuF r f)
nuR' p = wkR' p >>> nuL init
