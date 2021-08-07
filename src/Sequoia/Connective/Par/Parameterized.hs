module Sequoia.Connective.Par.Parameterized
( -- * Par
  Par(..)
) where

import Sequoia.Profunctor.Continuation

-- Par

newtype Par r a b = Par ((a • r, b • r) • r)
