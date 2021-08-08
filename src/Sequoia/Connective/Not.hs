{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Connective.Not
( -- * Not
  Not(..)
, type (¬)
) where

import Data.Distributive
import Data.Functor.Identity
import Data.Functor.Rep as Co
import Data.Profunctor
import Data.Profunctor.Rep as Pro
import Data.Profunctor.Sieve
import Sequoia.Connective.Bottom
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Not

newtype Not a r = Not { getNot :: a • Bottom r }
  deriving (Functor)
  deriving (Co.Representable) via ((•) a)
  deriving (Continuation, ContinuationE, ContinuationI, Corepresentable, Costrong, Profunctor, Pro.Representable, Strong) via (•)

instance Distributive (Not a) where
  distribute = distributeRep
  collect = collectRep

instance Sieve Not Identity where
  sieve = rmap Identity . (•)

instance Cosieve Not Identity where
  cosieve = lmap runIdentity . (•)

instance Pos a => Polarized N (Not a r) where


type (¬) = Not

infixr 9 ¬
