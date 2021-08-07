{-# LANGUAGE FunctionalDependencies #-}
module Sequoia.Biadjunction
( -- * Biadjunctions
  Biadjunction(..)
  -- * Defaults
, bileftAdjunctDisjConj
) where

import Data.Bifunctor
import Sequoia.Birepresentable
import Sequoia.Conjunction
import Sequoia.Disjunction

-- Biadjunctions

class (Bifunctor f, Birepresentable u) => Biadjunction f u | f -> u, u -> f where
  bileftAdjunct :: (f a a -> b) -> (a -> u b b)
  birightAdjunct :: (a -> u b b) -> (f a a -> b)

instance Biadjunction Either (,) where
  bileftAdjunct  f = f . inl >---< f . inr
  birightAdjunct f = exl . f <--> exr . f


-- Defaults

bileftAdjunctDisjConj :: (Disj f, Conj u) => (f a a -> b) -> (a -> u b b)
bileftAdjunctDisjConj f = f . inl >---< f . inr
