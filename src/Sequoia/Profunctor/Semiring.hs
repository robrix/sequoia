module Sequoia.Profunctor.Semiring
( -- * Semigroups
  ProfunctorPlus(..)
  -- * Monoids
, ProfunctorZero(..)
) where

import Data.Profunctor

-- Semigroups

class Profunctor p => ProfunctorPlus p where
  (<|>) :: p a b -> p a b -> p a b


-- Monoids

class ProfunctorPlus p => ProfunctorZero p where
  zero :: p a b
