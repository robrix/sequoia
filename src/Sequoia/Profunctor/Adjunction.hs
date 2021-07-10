{-# LANGUAGE FunctionalDependencies #-}
module Sequoia.Profunctor.Adjunction
( Adjunction(..)
, cosieveAdjunction
, cotabulateAdjunction
, Coadjunction(..)
, sieveCoadjunction
, tabulateCoadjunction
) where

import           Data.Profunctor
import qualified Data.Profunctor.Rep as Pro

-- | A covariant adjunction between two profunctors.
class (Profunctor f, Pro.Corepresentable u) => Adjunction f u | f -> u, u -> f where
  {-# MINIMAL (leftUnit | leftAdjunct), (rightUnit | rightAdjunct) #-}

  leftUnit  :: a -> u b (f b a)
  rightUnit :: f b (u b a) -> a

  leftUnit  = leftAdjunct  id
  rightUnit = rightAdjunct id

  leftAdjunct  :: (f a b ->     c) -> (    b -> u a c)
  rightAdjunct :: (    b -> u a c) -> (f a b ->     c)

  leftAdjunct  f = rmap f . leftUnit
  rightAdjunct f = rightUnit . rmap f


cosieveAdjunction :: Adjunction f u => u a b -> (f a c -> b)
cosieveAdjunction = rightAdjunct . const

cotabulateAdjunction :: Adjunction f u => (f a () -> b) -> u a b
cotabulateAdjunction f = leftAdjunct f ()


-- | A contravariant adjunction between two profunctors.
class (Profunctor f, Pro.Representable u) => Coadjunction f u | f -> u, u -> f where
  {-# MINIMAL (leftCounit | leftCoadjunct), (rightCounit | rightCoadjunct) #-}

  leftCounit  :: a -> u (f a b) b
  rightCounit :: a -> f (u a b) b

  leftCounit  = leftCoadjunct  id
  rightCounit = rightCoadjunct id

  leftCoadjunct  :: (a -> f b c) -> (b -> u a c)
  rightCoadjunct :: (a -> u b c) -> (b -> f a c)

  leftCoadjunct  f = lmap f . leftCounit
  rightCoadjunct f = lmap f . rightCounit


sieveCoadjunction :: Coadjunction f u => u a b -> (a -> f c b)
sieveCoadjunction = rightCoadjunct . const

tabulateCoadjunction :: Coadjunction f u => (a -> f () b) -> u a b
tabulateCoadjunction f = leftCoadjunct f ()
