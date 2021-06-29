{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Calculus.ForAll
( -- * Universal quantification
  Universal(..)
, forAllR'
  -- * Connectives
, module Focalized.ForAll
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Calculus.Negation
import Focalized.ForAll
import Focalized.Polarity
import Focalized.Quantification
import Prelude hiding (init)

-- Universal quantification

class Universal r s | s -> r where
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
  :: (Weaken s, Exchange s, Universal r s, Negation r s, (Polarized n ==> Neg) f)
  =>                              _Γ -|s|- _Δ > ForAll r n f
  -- ----------------------------------------------------------
  -> (forall x . Polarized n x => _Γ -|s|- _Δ >            f x)
forAllR' p = wkR' p >>> forAllL (dneN init)
