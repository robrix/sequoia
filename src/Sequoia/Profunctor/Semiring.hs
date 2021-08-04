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
import Sequoia.Profunctor.Continuation

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
  (<.>) = (<*>)

instance ProfunctorTimes (-->) where
  f <.> a = F (\ k -> K (\ x -> runF f (K (\ bc -> runF a (lmap bc k) • x)) • x))


class Profunctor p => ProfunctorCotimes p where
  (<&>) :: p (a >-- c) b -> p a b -> p c b

  infixl 4 <&>

instance ProfunctorCotimes (-->) where
  f <&> a = F (\ k -> K (\ c -> runF f k • (runF a k :>-- c)))


-- Unital semirings

class ProfunctorTimes p => ProfunctorOne p where
  one :: b -> p a b

instance ProfunctorOne (->) where
  one = const

instance ProfunctorOne (-->) where
  one a = F (\ k -> K (\ _ -> k • a))


class ProfunctorCotimes p => ProfunctorCoOne p where
  coOne :: (a • Void) -> p a b

instance ProfunctorCoOne (-->) where
  coOne = F . const


-- Exponentials

newtype a --> b = F { runF :: (b • Void) -> (a • Void) }

infixr 0 -->

instance Profunctor (-->) where
  dimap f g = F . dimap (lmap g) (lmap f) . runF

instance Functor ((-->) a) where
  fmap = rmap

instance Applicative ((-->) a) where
  pure a = F (\ k -> K (\ _ -> k • a))
  f <*> a = F (\ k -> K (\ x -> runF f (K (\ bc -> runF a (lmap bc k) • x)) • x))


-- Coexponentials

data a >-- b = (a • Void) :>-- b
  deriving (Functor)

infixr 0 >--, :>--

instance Profunctor (>--) where
  dimap f g (a :>-- b) = lmap f a :>-- g b
