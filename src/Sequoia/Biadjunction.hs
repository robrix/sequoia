{-# LANGUAGE FunctionalDependencies #-}
module Sequoia.Biadjunction
( -- * Biadjunctions
  Biadjunction(..)
  -- * Defaults
, bileftAdjunctDisjConj
, birightAdjunctDisjConj
, leftAdjunctBiadjunction
, rightAdjunctBiadjunction
) where

import Data.Bifunctor
import Sequoia.Bifunctor.Join
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

birightAdjunctDisjConj :: (Disj f, Conj u) => (a -> u b b) -> (f a a -> b)
birightAdjunctDisjConj f = exl . f <--> exr . f

leftAdjunctBiadjunction :: Biadjunction f u => (Join f a -> b) -> (a -> Join u b)
leftAdjunctBiadjunction f = Join . bileftAdjunct (f . Join)

rightAdjunctBiadjunction :: Biadjunction f u => (a -> Join u b) -> (Join f a -> b)
rightAdjunctBiadjunction f = birightAdjunct (runJoin . f) . runJoin
