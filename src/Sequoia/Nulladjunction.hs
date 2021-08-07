{-# LANGUAGE FunctionalDependencies #-}
module Sequoia.Nulladjunction
( -- * Nullary adjunctions
  Nulladjunction(..)
) where

-- Nullary adjunctions

class Nulladjunction f u | f -> u, u -> f where
  nullleftAdjunct :: (f -> b) -> (a -> u)
  nullrightAdjunct :: (a -> u) -> (f -> b)
