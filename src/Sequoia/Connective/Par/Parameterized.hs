module Sequoia.Connective.Par.Parameterized
( -- * Par
  Par(..)
) where

import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Par

newtype Par r a b = Par ((a • r, b • r) • r)

instance (Neg a, Neg b) => Polarized N (Par r a b) where
