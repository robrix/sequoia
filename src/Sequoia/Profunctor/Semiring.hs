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
, ProfunctorCoOne(..)
  -- * Exponentials
, type (-->)(..)
  -- * Coexponentials
, type (>--)(..)
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

class Profunctor p => ProfunctorTimes p where
  (<.>) :: p a (b -> c) -> p a b -> p a c

  infixl 4 <.>

instance ProfunctorTimes (->) where
  f <.> a = \ x -> f x (a x)

instance ProfunctorTimes (-->) where
  f <.> a = F (\ k x -> runF f (\ bc -> runF a (k . bc) x) x)


class Profunctor p => ProfunctorCotimes p where
  (<&>) :: p (a >-- c) b -> p a b -> p c b

  infixl 4 <&>

instance ProfunctorCotimes (-->) where
  f <&> a = F (\ k c -> runF f k (runF a k :>-- c))


-- Unital semirings

class ProfunctorTimes p => ProfunctorOne p where
  one :: b -> p a b

instance ProfunctorOne (->) where
  one = const

instance ProfunctorOne (-->) where
  one a = F (\ k _ -> k a)


class ProfunctorCotimes p => ProfunctorCoOne p where
  coOne :: (a -> Void) -> p a b

instance ProfunctorCoOne (-->) where
  coOne k = F (\ _ a -> k a)


-- Exponentials

newtype a --> b = F { runF :: (b -> Void) -> (a -> Void) }
  deriving (Functor)

instance Profunctor (-->) where
  dimap f g = F . dimap (lmap g) (lmap f) . runF


-- Coexponentials

data a >-- b = (a -> Void) :>-- b
  deriving (Functor)

infixr 0 >--, :>--

instance Profunctor (>--) where
  dimap f g (a :>-- b) = lmap f a :>-- g b
