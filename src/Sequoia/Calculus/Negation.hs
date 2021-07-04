{-# LANGUAGE ConstraintKinds #-}
module Sequoia.Calculus.Negation
( -- * Negation
  NegationIntro
  -- * Re-exports
, module Sequoia.Calculus.Not
, module Sequoia.Calculus.Negate
, module Sequoia.Connective.Negation
  -- * Negative double negation
, dneN
, dniN
  -- * Positive double negation
, dneP
, dniP
) where

import Sequoia.Calculus.Context
import Sequoia.Calculus.Negate
import Sequoia.Calculus.Not
import Sequoia.Connective.Negation
import Sequoia.Polarity
import Prelude hiding (init)

-- Negation

type NegationIntro k s = (NotIntro k s, NegateIntro k s)


-- Negative double negation

dneN
  :: (NegationIntro k s, Neg a)
  =>     a < _Γ -|s|- _Δ
  -- -------------------
  -> k ¬-a < _Γ -|s|- _Δ
dneN = notL . negateR

dniN
  :: (NegationIntro k s, Neg a)
  => _Γ -|s|- _Δ > a
  -- -------------------
  -> _Γ -|s|- _Δ > k ¬-a
dniN = notR . negateL


-- Positive double negation

dneP
  :: (NegationIntro k s, Pos a)
  =>     a < _Γ -|s|- _Δ
  -- -------------------
  -> k -¬a < _Γ -|s|- _Δ
dneP = negateL . notR

dniP
  :: (NegationIntro k s, Pos a)
  => _Γ -|s|- _Δ > a
  -- -------------------
  -> _Γ -|s|- _Δ > k -¬a
dniP = negateR . notL
