{-# LANGUAGE FunctionalDependencies #-}
module Sequoia.Biadjunction
( -- * Biadjunctions
  Biadjunction(..)
) where

import Data.Bifunctor
import Sequoia.Birepresentable

-- Biadjunctions

class (Bifunctor f, Birepresentable u) => Biadjunction f u | f -> u, u -> f where
  bileftAdjunct :: (f a a -> b) -> (a -> u b b)
  birightAdjunct :: (a -> u b b) -> (f a a -> b)
