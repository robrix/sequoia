{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Value
( -- * Value profunctor
  type (∘)(..)
  -- * Value abstraction
, Value(..)
  -- * Construction
, idV
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
import Fresnel.Iso
import Sequoia.Monad.Run

-- Value profunctor

newtype e ∘ a = V (e -> a)
  deriving (Applicative, Category, Choice, Closed, Cochoice, Pro.Corepresentable, Costrong, Functor, Mapping, Monad, MonadRun, Profunctor, Co.Representable, Pro.Representable, Strong, Traversing)

instance Distributive ((∘) e) where
  distribute = distributeRep
  collect = collectRep

instance Sieve (∘) Identity where
  sieve = rmap Identity . flip (∘)

instance Cosieve (∘) Identity where
  cosieve = lmap runIdentity . flip (∘)

instance Value (∘) where
  inV = V
  e ∘ V v = v e


-- Value abstraction

class Profunctor v => Value v where
  inV :: (e -> a) -> v e a
  (∘) :: e -> (v e a -> a)

  infixl 8 ∘


-- Construction

idV :: e ∘ e
idV = V id


-- Coercion

_V :: Iso (e ∘ a) (e' ∘ a') (e -> a) (e' -> a')
_V = coerced
