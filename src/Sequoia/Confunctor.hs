-- | Like a profunctor, but with opposite variances.
module Sequoia.Confunctor
( Confunctor(..)
, Flip(..)
) where

class Confunctor p where
  {-# MINIMAL conmap | (mapl, mapr) #-}

  conmap :: (a -> a') -> (b' -> b) -> ((a `p` b) -> (a' `p` b'))
  conmap f g = mapl f . mapr g

  mapl :: (a -> a') -> ((a `p` b) -> (a' `p` b))
  mapl = (`conmap` id)

  mapr :: (b' -> b) -> ((a `p` b) -> (a `p` b'))
  mapr = (id `conmap`)


-- FIXME: use Flip from bifunctors instead

newtype Flip p a b = Flip { runFlip :: p b a }
