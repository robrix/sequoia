{-# LANGUAGE ConstraintKinds #-}
module Sequoia.Calculus.Recursive
( -- * Recursion rules
  RecursiveIntro
  -- * Re-exports
, module Sequoia.Calculus.Mu
, module Sequoia.Calculus.Nu
) where

import Sequoia.Calculus.Mu
import Sequoia.Calculus.Nu

type RecursiveIntro k v s = (NuIntro k v s, MuIntro k v s)
