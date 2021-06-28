{-# LANGUAGE ConstraintKinds #-}
module Focalized.Calculus.Shift
( -- * Shifts
  Shift
  -- * Connectives
, module Focalized.Calculus.Down
, module Focalized.Calculus.Up
) where

import Focalized.Calculus.Down
import Focalized.Calculus.Up

type Shift s = (NegShift s, PosShift s)
