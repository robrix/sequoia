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
import Sequoia.Calculus.Structural
import Sequoia.Connective.Nu
import Sequoia.Connective.Quantification
import Sequoia.Polarity

-- Corecursion

class Core s => NuIntro s where
  nuL
    :: (Pos ==> Neg) f
    => Exists r P (NuF e r f) < _Γ ⊣s e r⊢ _Δ
    -- ----------------------------------------
    ->             Nu  e r f  < _Γ ⊣s e r⊢ _Δ

  nuR
    :: (Pos ==> Neg) f
    => _Γ ⊣s e r⊢ _Δ > Exists r P (NuF e r f)
    -- ----------------------------------------
    -> _Γ ⊣s e r⊢ _Δ >             Nu  e r f


nuR'
  :: (Weaken s, Exchange s, NuIntro s, (Pos ==> Neg) f)
  => _Γ ⊣s e r⊢ _Δ >             Nu  e r f
  -- ----------------------------------------
  -> _Γ ⊣s e r⊢ _Δ > Exists r P (NuF e r f)
nuR' p = wkR' p >>> nuL init
