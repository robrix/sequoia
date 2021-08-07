module Sequoia.Connective.Par.Parameterized
( -- * Par
  Par(..)
  -- * Elimination
, runPar
) where

import Sequoia.Conjunction
import Sequoia.Disjunction
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Par

newtype Par r a b = Par ((a • r, b • r) • r)

instance (Neg a, Neg b) => Polarized N (Par r a b) where

instance DisjIn (Par r) where
  inl l = Par (exlL (dn l))
  inr r = Par (exrL (dn r))


-- Elimination

runPar :: (a • r, b • r) -> Par r a b • r
runPar e = K (\ (Par r) -> r • e)
