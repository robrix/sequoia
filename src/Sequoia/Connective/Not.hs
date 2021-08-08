{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Connective.Not
( -- * Not
  Not(..)
, type (¬)
) where

import Data.Functor.Identity
import Data.Profunctor
import Data.Profunctor.Rep
import Data.Profunctor.Sieve
import Sequoia.Connective.Bottom
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Not

newtype Not a r = Not { getNot :: a • Bottom r }
  deriving (Functor)
  deriving (Continuation, ContinuationE, ContinuationI, Corepresentable, Costrong, Profunctor) via (•)

instance Sieve Not Identity where
  sieve = rmap Identity . (•)

instance Cosieve Not Identity where
  cosieve = lmap runIdentity . (•)

instance Pos a => Polarized N (Not a r) where


type (¬) = Not

infixr 9 ¬
