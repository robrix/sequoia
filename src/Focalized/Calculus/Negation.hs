{-# LANGUAGE ConstraintKinds #-}
module Focalized.Calculus.Negation
( -- * Negation
  Negation
  -- * Re-exports
, module Focalized.Calculus.Not
, module Focalized.Calculus.Negate
  -- * Negative double negation
, dneN
, dniN
  -- * Positive double negation
, dneP
, dniP
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Negate
import Focalized.Calculus.Not
import Focalized.Polarity
import Prelude hiding (init)

-- Negation

type Negation s = (NegNegation s, PosNegation s)


-- Negative double negation

dneN
  :: (NegNegation s, PosNegation s, Neg a)
  =>     a < i -|s r|- o
  -- -------------------
  -> r ¬-a < i -|s r|- o
dneN = notL . negateR

dniN
  :: (NegNegation s, PosNegation s, Neg a)
  => i -|s r|- o > a
  -- -------------------
  -> i -|s r|- o > r ¬-a
dniN = notR . negateL


-- Positive double negation

dneP
  :: (NegNegation s, PosNegation s, Pos a)
  =>     a < i -|s r|- o
  -- -------------------
  -> r -¬a < i -|s r|- o
dneP = negateL . notR

dniP
  :: (NegNegation s, PosNegation s, Pos a)
  => i -|s r|- o > a
  -- -------------------
  -> i -|s r|- o > r -¬a
dniP = negateR . notL
