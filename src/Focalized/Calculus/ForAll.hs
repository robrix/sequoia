{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Calculus.ForAll
( -- * Universal quantification
  UniversalIntro(..)
, forAllR'
  -- * Connectives
, module Focalized.Connective.ForAll
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Calculus.Negation
import Focalized.Connective.ForAll
import Focalized.Connective.Quantification
import Focalized.Continuation
import Focalized.Polarity
import Prelude hiding (init)

-- Universal quantification

class Core s => UniversalIntro s where
  forAllL
    :: (Polarized n x, Neg (f x))
    =>              K s ¬-f x < _Γ -|s|- _Δ
    -- ------------------------------------
    -> ForAll (R (K s)) n f   < _Γ -|s|- _Δ

  forAllR
    :: (Polarized n ==> Neg) f
    => (forall x . Polarized n x => _Γ -|s|- _Δ >                    f x)
    -- ------------------------------------------------------------------
    ->                              _Γ -|s|- _Δ > ForAll (R (K s)) n f


forAllR'
  :: (Weaken s, Exchange s, UniversalIntro s, NegationIntro s, (Polarized n ==> Neg) f)
  =>                              _Γ -|s|- _Δ > ForAll (R (K s)) n f
  -- ------------------------------------------------------------------
  -> (forall x . Polarized n x => _Γ -|s|- _Δ >                    f x)
forAllR' p = wkR' p >>> forAllL (dneN init)
