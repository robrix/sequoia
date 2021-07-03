{-# LANGUAGE ConstraintKinds #-}
module Focalized.Calculus.Shift
( -- * Shifts
  ShiftIntro
  -- * Connectives
, module Focalized.Calculus.Down
, module Focalized.Calculus.Up
) where

import Focalized.Calculus.Down
import Focalized.Calculus.Up

type ShiftIntro k s = (UpIntro k s, DownIntro k s)
