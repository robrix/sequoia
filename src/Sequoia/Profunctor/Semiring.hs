{-# LANGUAGE FunctionalDependencies #-}
module Sequoia.Profunctor.Semiring
( -- * Semigroups
  RSemigroup(..)
  -- * Monoids
, RMonoid(..)
  -- * Semirings
, RApply(..)
, LApply(..)
, ProfunctorApply(..)
  -- * Unital semirings
, ROne(..)
, LOne(..)
, ProfunctorOne(..)
) where

import Data.Profunctor
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Exp

-- Semigroups

class Profunctor p => RSemigroup p where
  (<|>) :: p a b -> p a b -> p a b

  infixl 3 <|>


-- Monoids

class RSemigroup p => RMonoid p where
  zero :: p a b


-- Semirings

class Profunctor p => RApply p where
  (<.>) :: p a (b -> c) -> p a b -> p a c

  infixl 4 <.>

instance RApply (->) where
  (<.>) = (<*>)

instance RApply (Exp r) where
  (<.>) = (<*>)


class Profunctor p => LApply r p | p -> r where
  (<&>) :: p (Coexp r a c) b -> p a b -> p c b

  infixl 4 <&>

instance LApply r (Exp r) where
  f <&> a = Exp (\ k c -> getExp f k (getExp a k :>- c))


class (LApply r p, RApply p) => ProfunctorApply r p where
  (<&.>) :: p (Coexp r a b) (c -> d) -> (p a c -> p b d)

  infixl 4 <&.>


-- Unital semirings

class RApply p => ROne p where
  rpure :: b -> p a b

instance ROne (->) where
  rpure = pure

instance ROne (Exp r) where
  rpure = pure


class LApply r p => LOne r p | p -> r where
  lpure :: (a • r) -> p a b

instance LOne r (Exp r) where
  lpure = Exp . const . (•)


class (LOne r p, ROne p) => ProfunctorOne r p | p -> r where
  dipure :: Coexp r a b -> p a b
