{-# LANGUAGE FunctionalDependencies #-}
module Sequoia.Profunctor.Adjunction
( Adjunction(..)
) where

import Data.Profunctor

class (Profunctor f, Profunctor u) => Adjunction f u | f -> u, u -> f where
  {-# MINIMAL (leftUnit | leftAdjunct), (rightUnit | rightAdjunct) #-}

  leftUnit  :: a -> u b (f b a)
  rightUnit :: f b (u b a) -> a

  leftUnit  = leftAdjunct id
  rightUnit = rightAdjunct id

  leftAdjunct  :: (f a b ->     c) -> (    b -> u a c)
  rightAdjunct :: (    b -> u a c) -> (f a b ->     c)

  leftAdjunct  f = rmap f . leftUnit
  rightAdjunct f = rightUnit . rmap f
