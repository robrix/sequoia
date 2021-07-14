{-# LANGUAGE QuantifiedConstraints #-}
module Sequoia.Calculus.Nu
( -- * Corecursion
  NuIntro(..)
, nuR'
  -- * Connectives
, module Sequoia.Connective.Nu
) where

import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Connective.Nu
import Sequoia.Connective.Quantification
import Sequoia.Polarity

-- Corecursion

class Core k v s => NuIntro k v s where
  nuL
    :: (Pos ==> Neg) f
    => Exists k P (NuF k f) < _Γ -|s|- _Δ
    -- ----------------------------------
    ->             Nu  k f  < _Γ -|s|- _Δ

  nuR
    :: (Pos ==> Neg) f
    => _Γ -|s|- _Δ > Exists k P (NuF k f)
    -- ----------------------------------
    -> _Γ -|s|- _Δ >             Nu  k f


nuR'
  :: (Weaken k v s, Exchange k v s, NuIntro k v s, (Pos ==> Neg) f)
  => _Γ -|s|- _Δ >             Nu  k f
  -- ----------------------------------
  -> _Γ -|s|- _Δ > Exists k P (NuF k f)
nuR' p = wkR' p >>> nuL init
