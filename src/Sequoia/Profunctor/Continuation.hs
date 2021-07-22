{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Continuation
( -- * Continuation profunctor
  K(..)
  -- * Composition
, (<••>)
) where

import Control.Category (Category)
import Data.Distributive
import Data.Functor.Identity
import Data.Functor.Rep as Co
import Data.Profunctor
import Data.Profunctor.Rep as Pro
import Data.Profunctor.Sieve
import Data.Profunctor.Traversing
import Sequoia.Disjunction

-- Continuation profunctor

newtype K a r = K { (•) :: a -> r }
  deriving (Applicative, Category, Choice, Closed, Cochoice, Pro.Corepresentable, Costrong, Functor, Mapping, Monad, Profunctor, Co.Representable, Pro.Representable, Strong, Traversing)

infixl 7 •

instance Distributive (K r) where
  distribute = distributeRep
  collect = collectRep

instance Sieve K Identity where
  sieve = rmap Identity . (•)

instance Cosieve K Identity where
  cosieve = lmap runIdentity . (•)


-- Composition

(<••>) :: Disj d => K a r -> K b r -> K (a `d` b) r
a <••> b = K ((a •) <--> (b •))

infix 3 <••>
