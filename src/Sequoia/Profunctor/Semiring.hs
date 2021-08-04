module Sequoia.Profunctor.Semiring
( -- * Semigroups
  ProfunctorPlus(..)
) where

import Data.Profunctor

-- Semigroups

class Profunctor p => ProfunctorPlus p where
  (<|>) :: p a b -> p a b -> p a b
