{-# LANGUAGE QuantifiedConstraints #-}
module Focalized.Calculus.Recursion
( -- * Corecursion
  Corecursion(..)
, nuR'
  -- * Recursion
, Recursion(..)
, muL'
  -- * Connectives
, module Focalized.Recursion
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Calculus.Quantification
import Focalized.Implication
import Focalized.Polarity
import Focalized.Recursion
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
