{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Calculus.Exists
( -- * Existential quantification
  ExistentialIntro(..)
, existsL'
  -- * Connectives
, module Sequoia.Connective.Exists
) where

import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Connective.Exists
import Sequoia.Connective.Quantification
import Sequoia.Polarity
import Prelude hiding (init)

-- Existential quantification

class Core k s => ExistentialIntro k s where
  existsL
    :: (forall x . Polarized n x => f x < _Γ -|s|- _Δ)
    -- -----------------------------------------------
    ->                   Exists k n f   < _Γ -|s|- _Δ

  existsR
    :: (Polarized n x, Pos (f x))
    => _Γ -|s|- _Δ >            f x
    -- ----------------------------
    -> _Γ -|s|- _Δ > Exists k n f


existsL'
  :: (Weaken k s, Exchange k s, ExistentialIntro k s, (Polarized n ==> Pos) f)
  =>                   Exists k n f   < _Γ -|s|- _Δ
  -- -----------------------------------------------
  -> (forall x . Polarized n x => f x < _Γ -|s|- _Δ)
existsL' p = existsR init >>> wkL' p
