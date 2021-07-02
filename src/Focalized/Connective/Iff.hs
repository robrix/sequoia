module Focalized.Connective.Iff
( -- * Logical biconditional
  Iff(..)
) where

import Focalized.CPS

-- Logical biconditional

data Iff r a b
  = IffT a b
  | IffF (r •a) (r •b)
