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

class UniversalIntro s where
  forAllL
    :: (Polarized n x, Neg (f x))
    =>        r ¬-f x < _Γ -|s r|- _Δ
    -- ------------------------------
    -> ForAll r n f   < _Γ -|s r|- _Δ

  forAllR
    :: (Polarized n ==> Neg) f
    => (forall x . Polarized n x => _Γ -|s r|- _Δ >            f x)
    -- ------------------------------------------------------------
    ->                              _Γ -|s r|- _Δ > ForAll r n f


forAllR'
  :: (Weaken s, Exchange s, UniversalIntro s, NegationIntro s, (Polarized n ==> Neg) f)
  =>                              _Γ -|s r|- _Δ > ForAll r n f
  -- ------------------------------------------------------------------------
  -> (forall x . Polarized n x => _Γ -|s r|- _Δ >            f x)
forAllR' p = wkR' p >>> forAllL (dneN init)
