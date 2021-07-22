{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Value
( -- * Value profunctor
  V(..)
  -- * Coercion
, _V
) where

import Control.Category (Category)
import Data.Distributive
import Data.Functor.Identity
import Data.Functor.Rep as Co
import Data.Profunctor
import Data.Profunctor.Rep as Pro
import Data.Profunctor.Sieve
import Data.Profunctor.Traversing
import Sequoia.Optic.Iso

-- Value profunctor

newtype V e a = V { (∘) :: e -> a }
  deriving (Applicative, Category, Choice, Closed, Cochoice, Pro.Corepresentable, Costrong, Functor, Mapping, Monad, Profunctor, Co.Representable, Pro.Representable, Strong, Traversing)

infix 8 ∘

instance Distributive (V e) where
  distribute = distributeRep
  collect = collectRep

instance Sieve V Identity where
  sieve = rmap Identity . (∘)

instance Cosieve V Identity where
  cosieve = lmap runIdentity . (∘)


-- Coercion

_V :: Iso (V e a) (V e' a') (e -> a) (e' -> a')
_V = coerced
