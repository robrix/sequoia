{-# LANGUAGE ConstraintKinds #-}
module Sequoia.Calculus.Assertion
( -- * Assertion
  AssertionIntro
  -- * Re-exports
, module Sequoia.Calculus.Yes
) where

import Sequoia.Calculus.Yes

type AssertionIntro s = Yes s
