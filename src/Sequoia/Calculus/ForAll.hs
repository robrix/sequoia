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

class Core k v s => UniversalIntro k v s where
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
  :: (Weaken k v s, Exchange k v s, UniversalIntro k v s, NegationIntro k v s, (Polarized n ==> Neg) f)
  =>                              _Γ -|s|- _Δ > ForAll k n f
  -- ----------------------------------------------------------
  -> (forall x . Polarized n x => _Γ -|s|- _Δ >            f x)
forAllR' p = wkR' p >>> forAllL (dneN init)
