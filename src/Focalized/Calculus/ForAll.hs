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
import Focalized.Polarity
import Prelude hiding (init)

-- Universal quantification

class Core k s => UniversalIntro k s where
  forAllL
    :: (Polarized n x, Neg (f x))
    =>        k ¬-f x < _Γ -|s|- _Δ
    -- ----------------------------
    -> ForAll k n f   < _Γ -|s|- _Δ

  forAllR
    :: (Polarized n ==> Neg) f
    => (forall x . Polarized n x => _Γ -|s|- _Δ >            f x)
    -- ----------------------------------------------------------
    ->                              _Γ -|s|- _Δ > ForAll k n f


forAllR'
  :: (Weaken k s, Exchange k s, UniversalIntro k s, NegationIntro k s, (Polarized n ==> Neg) f)
  =>                              _Γ -|s|- _Δ > ForAll k n f
  -- ----------------------------------------------------------
  -> (forall x . Polarized n x => _Γ -|s|- _Δ >            f x)
forAllR' p = wkR' p >>> forAllL (dneN init)
