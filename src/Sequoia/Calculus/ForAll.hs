{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Calculus.ForAll
( -- * Universal quantification
  UniversalIntro(..)
, forAllR'
  -- * Connectives
, module Sequoia.Connective.ForAll
) where

import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Calculus.Negation
import Sequoia.Connective.ForAll
import Sequoia.Connective.Quantification
import Sequoia.Polarity

-- Universal quantification

class Core e r s => UniversalIntro e r s where
  forAllL
    :: (Polarized n x, Neg (f x))
    =>        r ¬-f x < _Γ -|s|- _Δ
    -- ----------------------------
    -> ForAll r n f   < _Γ -|s|- _Δ

  forAllR
    :: (Polarized n ==> Neg) f
    => (forall x . Polarized n x => _Γ -|s|- _Δ >            f x)
    -- ----------------------------------------------------------
    ->                              _Γ -|s|- _Δ > ForAll r n f


forAllR'
  :: (Weaken e r s, Exchange e r s, UniversalIntro e r s, NegationIntro e r s, (Polarized n ==> Neg) f)
  =>                              _Γ -|s|- _Δ > ForAll r n f
  -- ----------------------------------------------------------
  -> (forall x . Polarized n x => _Γ -|s|- _Δ >            f x)
forAllR' p = wkR' p >>> forAllL (dneN init)
