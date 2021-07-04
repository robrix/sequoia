{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Calculus.ForAll
( -- * Universal quantification
  UniversalIntro(..)
, forAllR'
  -- * Connectives
, module Sequoia.Connective.ForAll
) where

import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Calculus.Negation
import Sequoia.Connective.ForAll
import Sequoia.Connective.Quantification
import Sequoia.Polarity
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
