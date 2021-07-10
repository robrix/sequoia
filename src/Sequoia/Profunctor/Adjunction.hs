module Sequoia.Profunctor.Adjunction
( Adjunction(..)
) where

class Adjunction f u where
  leftAdjunct  :: (f b a -> c) -> (a -> u b c)
  rightAdjunct :: (c -> u a b) -> (f a c -> b)
