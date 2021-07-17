{-# LANGUAGE ConstraintKinds #-}
module Sequoia.Calculus.Shift
( -- * Shifts
  ShiftIntro
  -- * Connectives
, module Sequoia.Calculus.Down
, module Sequoia.Calculus.Up
) where

import Sequoia.Calculus.Down
import Sequoia.Calculus.Up

type ShiftIntro s = (UpIntro s, DownIntro s)
