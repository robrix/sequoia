{-# LANGUAGE ConstraintKinds #-}
module Focalized.Calculus.Recursive
( -- * Recursion rules
  RecursiveIntro
  -- * Re-exports
, module Focalized.Calculus.Mu
, module Focalized.Calculus.Nu
) where

import Focalized.Calculus.Mu
import Focalized.Calculus.Nu

type RecursiveIntro k s = (NuIntro k s, MuIntro k s)
