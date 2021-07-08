-- | Like a profunctor, but with opposite variances.
module Sequoia.Confunctor
( Confunctor(..)
, Flip(..)
  -- * Deriving
, Profunctorially(..)
, Confunctorially(..)
) where

import Data.Functor.Contravariant
import Data.Profunctor

class Confunctor p where
  {-# MINIMAL conmap | (mapl, mapr) #-}

  conmap :: (a -> a') -> (b' -> b) -> ((a `p` b) -> (a' `p` b'))
  conmap f g = mapl f . mapr g

  mapl :: (a -> a') -> ((a `p` b) -> (a' `p` b))
  mapl = (`conmap` id)

  mapr :: (b' -> b) -> ((a `p` b) -> (a `p` b'))
  mapr = (id `conmap`)


newtype Flip p a b = Flip { runFlip :: p b a }
  deriving Contravariant via Confunctorially (Flip p) a

instance Confunctor p => Functor (Flip p a) where
  fmap = rmap

instance Confunctor p => Profunctor (Flip p) where
  dimap f g = Flip . conmap g f . runFlip

instance Profunctor p => Confunctor (Flip p) where
  conmap f g = Flip . dimap g f . runFlip


-- Deriving

newtype Profunctorially p a b = Profunctorially { runProfunctorially :: p a b }


newtype Confunctorially p a b = Confunctorially { runConfunctorially :: p a b }
  deriving (Confunctor)

instance Confunctor p => Contravariant (Confunctorially p a) where
  contramap = mapr
