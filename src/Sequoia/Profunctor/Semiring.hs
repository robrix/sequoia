module Sequoia.Profunctor.Semiring
( -- * Semigroups
  ProfunctorPlus(..)
  -- * Monoids
, ProfunctorZero(..)
  -- * Semirings
, RApplicative(..)
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

class Profunctor p => RApplicative p where
  (<.>) :: p a (b -> c) -> p a b -> p a c

  infixl 4 <.>

instance RApplicative (->) where
  (<.>) = (<*>)

instance RApplicative (-->) where
  (<.>) = (<*>)


class Profunctor p => ProfunctorCotimes p where
  (<&>) :: p (a >-- c) b -> p a b -> p c b

  infixl 4 <&>

instance ProfunctorCotimes (-->) where
  f <&> a = F (\ k -> K (\ c -> runF f k • (runF a k :>-- c)))


-- Unital semirings

class RApplicative p => ProfunctorOne p where
  rpure :: b -> p a b

instance ProfunctorOne (->) where
  rpure = pure

instance ProfunctorOne (-->) where
  rpure = pure


class ProfunctorCotimes p => ProfunctorCoOne p where
  lpure :: (a • Void) -> p a b

instance ProfunctorCoOne (-->) where
  lpure = F . const


-- Exponentials

newtype a --> b = F { runF :: (b • Void) -> (a • Void) }

infixr 0 -->

instance Profunctor (-->) where
  dimap f g = F . dimap (lmap g) (lmap f) . runF

instance Functor ((-->) a) where
  fmap = rmap

instance Applicative ((-->) a) where
  pure a = F (K . const . (• a))
  f <*> a = F (\ k -> K (\ x -> runF f (K (\ bc -> runF a (lmap bc k) • x)) • x))


-- Coexponentials

data a >-- b = (a • Void) :>-- b
  deriving (Functor)

infixr 0 >--, :>--

instance Profunctor (>--) where
  dimap f g (a :>-- b) = lmap f a :>-- g b
