module Sequoia.Profunctor.Semiring
( -- * Semigroups
  ProfunctorPlus(..)
  -- * Monoids
, ProfunctorZero(..)
  -- * Semirings
, ProfunctorTimes(..)
, ProfunctorCotimes(..)
  -- * Unital semirings
, ProfunctorOne(..)
) where

import Data.Profunctor
import Data.Void

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


class Profunctor p => ProfunctorCotimes p where
  (<&>) :: p (a >- c) b -> p a b -> p c b

  infixl 4 <&>


-- Unital semirings

class (ProfunctorTimes p, ProfunctorZero p) => ProfunctorOne p where
  one :: b -> p a b



data a >- b = (a -> Void) :>- b
  deriving Functor

infixr 0 >-, :>-

instance Profunctor (>-) where
  dimap f g (a :>- b) = lmap f a :>- g b
