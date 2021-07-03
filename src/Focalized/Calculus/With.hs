module Focalized.Calculus.With
( -- * With
  WithIntro(..)
, withR1'
, withR2'
, withIdentityL
, withIdentityR
, withAssociativity
, withCommutativity
  -- * Connectives
, module Focalized.Connective.With
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Calculus.Top
import Focalized.Connective.With
import Focalized.Polarity
import Prelude hiding (init)

-- With

class Core s => WithIntro s where
  withL1
    :: (Neg a, Neg b)
    => a     < _Γ -|s|- _Δ
    -- -------------------
    -> a & b < _Γ -|s|- _Δ

  withL2
    :: (Neg a, Neg b)
    =>     b < _Γ -|s|- _Δ
    -- -------------------
    -> a & b < _Γ -|s|- _Δ

  withR, (⊢&)
    :: (Neg a, Neg b)
    => _Γ -|s|- _Δ > a   ->   _Γ -|s|- _Δ > b
    -- --------------------------------------
    ->           _Γ -|s|- _Δ > a & b
  (⊢&) = withR

  infixr 6 ⊢&


withR1'
  :: (Weaken s, Exchange s, WithIntro s, Neg a, Neg b)
  => _Γ -|s|- _Δ > a & b
  -- -----s-------------
  -> _Γ -|s|- _Δ > a
withR1' t = wkR' t >>> withL1 init

withR2'
  :: (Weaken s, Exchange s, WithIntro s, Neg a, Neg b)
  => _Γ -|s|- _Δ > a & b
  -- -------------------
  -> _Γ -|s|- _Δ > b
withR2' t = wkR' t >>> withL2 init


withIdentityL
  :: (WithIntro s, Neg a)
  -- --------------------------
  => Top & a < _Γ -|s|- _Δ > a
withIdentityL = withL2 init

withIdentityR
  :: (WithIntro s, TopIntro s, Neg a)
  -- --------------------------
  => a < _Γ -|s|- _Δ > a & Top
withIdentityR = init ⊢& topR

withAssociativity
  :: (WithIntro s, Neg a, Neg b, Neg c)
  -- ---------------------------------------
  => a & (b & c) < _Γ -|s|- _Δ > (a & b) & c
withAssociativity = (withL1 init ⊢& withL2 (withL1 init)) ⊢& withL2 (withL2 init)

withCommutativity
  :: (Exchange s, WithIntro s, Neg a, Neg b)
  -- ---------------------------
  => a & b < _Γ -|s|- _Δ > b & a
withCommutativity = withL2 init ⊢& withL1 init
