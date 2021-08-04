{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Value
( -- * Value profunctor
  type (∘)(..)
  -- * Construction
, idV
  -- * Elimination
, (∘)
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

infixl 8 ∘

instance Distributive ((∘) e) where
  distribute = distributeRep
  collect = collectRep

instance Sieve (∘) Identity where
  sieve = rmap Identity . flip (∘)

instance Cosieve (∘) Identity where
  cosieve = lmap runIdentity . flip (∘)


-- Construction

idV :: e ∘ e
idV = V id


-- Elimination

(∘) :: e -> e ∘ a -> a
e ∘ V v = v e


-- Coercion

_V :: Iso (e ∘ a) (e' ∘ a') (e -> a) (e' -> a')
_V = coerced
