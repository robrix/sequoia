{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Calculus.ForAll
( -- * Universal quantification
  Universal(..)
, forAllR'
  -- * Connectives
, module Focalized.Quantification
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Calculus.Negation
import Focalized.Polarity
import Focalized.Quantification
import Prelude hiding (init)

-- Universal quantification

class Universal s where
  forAllL
    :: (Polarized n x, Neg (f x))
    =>        r ¬-f x < i -|s r|- o
    -- ----------------------------
    -> ForAll r n f   < i -|s r|- o

  forAllR
    :: (Polarized n ==> Neg) f
    => (forall x . Polarized n x => i -|s r|- o >            f x)
    -- ---------------------------------------
    ->                              i -|s r|- o > ForAll r n f


forAllR'
  :: (Weaken s, Exchange s, Universal s, Negation s, (Polarized n ==> Neg) f)
  =>                              i -|s r|- o > ForAll r n f
  -- ---------------------------------------
  -> (forall x . Polarized n x => i -|s r|- o >            f x)
forAllR' p = wkR' p >>> forAllL (dneN init)
