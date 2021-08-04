module Sequoia.Profunctor.Semiring
( -- * Semigroups
  ProfunctorPlus(..)
  -- * Monoids
, ProfunctorZero(..)
  -- * Semirings
, ProfunctorTimes(..)
  -- * Unital semirings
, ProfunctorOne(..)
) where

import Data.Profunctor

-- Semigroups

class Profunctor p => ProfunctorPlus p where
  (<|>) :: p a b -> p a b -> p a b

  infixl 3 <|>


-- Monoids

class ProfunctorPlus p => ProfunctorZero p where
  zero :: p a b


-- Semirings

class ProfunctorPlus p => ProfunctorTimes p where
  (<.>) :: p a (b -> c) -> p a b -> p a c

  infixl 4 <.>


-- Unital semirings

class (ProfunctorTimes p, ProfunctorZero p) => ProfunctorOne p where
  one :: b -> p a b
