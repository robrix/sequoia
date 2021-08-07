{-# LANGUAGE FunctionalDependencies #-}
-- | Adjunctions between nullary “functors”.
module Sequoia.Nulladjunction
( -- * Nullary adjunctions
  Nulladjunction(..)
) where

import Data.Void

-- Nullary adjunctions

class Nulladjunction f u | f -> u, u -> f where
  nullleftAdjunct :: (f -> b) -> (a -> u)
  nullrightAdjunct :: (a -> u) -> (f -> b)

instance Nulladjunction Void () where
  nullleftAdjunct _ _ = ()
  nullrightAdjunct _ = absurd
