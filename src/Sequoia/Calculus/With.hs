module Sequoia.Calculus.With
( -- * With
  WithIntro(..)
, withR1'
, withR2'
, withIdentityL
, withIdentityR
, withAssociativity
, withCommutativity
  -- * Connectives
, module Sequoia.Connective.With
) where

import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Calculus.Structural
import Sequoia.Calculus.Top
import Sequoia.Connective.With
import Sequoia.Polarity

-- With

class WithIntro s where
  withL1
    :: (Neg a, Neg b)
    => a     < _Γ -|s e r|- _Δ
    -- -----------------------
    -> a & b < _Γ -|s e r|- _Δ

  withL2
    :: (Neg a, Neg b)
    =>     b < _Γ -|s e r|- _Δ
    -- -----------------------
    -> a & b < _Γ -|s e r|- _Δ

  withR, (⊢&)
    :: (Neg a, Neg b)
    => _Γ -|s e r|- _Δ > a   ->   _Γ -|s e r|- _Δ > b
    -- ----------------------------------------------
    ->             _Γ -|s e r|- _Δ > a & b
  (⊢&) = withR

  infixr 6 ⊢&


withR1'
  :: (Weaken e r (s e r), Exchange e r (s e r), WithIntro s, Neg a, Neg b)
  => _Γ -|s e r|- _Δ > a & b
  -- -----------------------
  -> _Γ -|s e r|- _Δ > a
withR1' t = wkR' t >>> withL1 init

withR2'
  :: (Weaken e r (s e r), Exchange e r (s e r), WithIntro s, Neg a, Neg b)
  => _Γ -|s e r|- _Δ > a & b
  -- -----------------------
  -> _Γ -|s e r|- _Δ > b
withR2' t = wkR' t >>> withL2 init


withIdentityL
  :: (Core e r (s e r), WithIntro s, Neg a)
  -- -----------------------------
  => Top & a < _Γ -|s e r|- _Δ > a
withIdentityL = withL2 init

withIdentityR
  :: (WithIntro s, TopIntro e r (s e r), Neg a)
  -- -----------------------------
  => a < _Γ -|s e r|- _Δ > a & Top
withIdentityR = init ⊢& topR

withAssociativity
  :: (Core e r (s e r), WithIntro s, Neg a, Neg b, Neg c)
  -- -------------------------------------------
  => a & (b & c) < _Γ -|s e r|- _Δ > (a & b) & c
withAssociativity = (withL1 init ⊢& withL2 (withL1 init)) ⊢& withL2 (withL2 init)

withCommutativity
  :: (Exchange e r (s e r), WithIntro s, Neg a, Neg b)
  -- -------------------------------
  => a & b < _Γ -|s e r|- _Δ > b & a
withCommutativity = withL2 init ⊢& withL1 init
