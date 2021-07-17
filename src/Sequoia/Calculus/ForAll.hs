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
import Sequoia.Calculus.Structural
import Sequoia.Connective.ForAll
import Sequoia.Connective.Quantification
import Sequoia.Polarity

-- Universal quantification

class Core s => UniversalIntro s where
  forAllL
    :: (Polarized n x, Neg (f x))
    =>        r ¬-f x < _Γ -|s e r|- _Δ
    -- --------------------------------
    -> ForAll r n f   < _Γ -|s e r|- _Δ

  forAllR
    :: (Polarized n ==> Neg) f
    => (forall x . Polarized n x => _Γ -|s e r|- _Δ >            f x)
    -- --------------------------------------------------------------
    ->                              _Γ -|s e r|- _Δ > ForAll r n f


forAllR'
  :: (Weaken s, Exchange s, UniversalIntro s, NegationIntro s, (Polarized n ==> Neg) f)
  =>                              _Γ -|s e r|- _Δ > ForAll r n f
  -- --------------------------------------------------------------
  -> (forall x . Polarized n x => _Γ -|s e r|- _Δ >            f x)
forAllR' p = wkR' p >>> forAllL (dneN init)
