-- | Like a profunctor, but with opposite variances.
module Sequoia.Confunctor
( Confunctor(..)
, Flip(..)
  -- * Strength
, Contrastrong(..)
, Contracostrong(..)
  -- * Deriving
, Profunctorially(..)
, Confunctorially(..)
) where

import Data.Functor.Contravariant
import Data.Profunctor
import Data.Tuple (swap)

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
  deriving Functor via Profunctorially (Flip p) a

instance Confunctor p => Profunctor (Flip p) where
  dimap f g = Flip . conmap g f . runFlip

instance Profunctor p => Confunctor (Flip p) where
  conmap f g = Flip . dimap g f . runFlip

instance Contrastrong p => Strong (Flip p) where
  first'  = Flip . confirst  . runFlip
  second' = Flip . consecond . runFlip

instance Strong p => Contrastrong (Flip p) where
  confirst  = Flip . first'  . runFlip
  consecond = Flip . second' . runFlip

instance Contracostrong p => Costrong (Flip p) where
  unfirst  = Flip . conunfirst  . runFlip
  unsecond = Flip . conunsecond . runFlip

instance Costrong p => Contracostrong (Flip p) where
  conunfirst  = Flip . unfirst  . runFlip
  conunsecond = Flip . unsecond . runFlip


-- Strength

class Confunctor p => Contrastrong p where
  {-# MINIMAL confirst | consecond #-}
  confirst  :: p a b -> p (a, c) (b, c)
  confirst = conmap swap swap . consecond
  consecond :: p a b -> p (c, a) (c, b)
  consecond = conmap swap swap . confirst

class Confunctor p => Contracostrong p where
  {-# MINIMAL conunfirst | conunsecond #-}
  conunfirst  :: p (a, c) (b, c) -> p a b
  conunfirst = conunsecond . conmap swap swap
  conunsecond :: p (c, a) (c, b) -> p a b
  conunsecond = conunfirst . conmap swap swap


-- Deriving

newtype Profunctorially p a b = Profunctorially { runProfunctorially :: p a b }
  deriving (Profunctor)

instance Profunctor p => Functor (Profunctorially p a) where
  fmap = rmap


newtype Confunctorially p a b = Confunctorially { runConfunctorially :: p a b }
  deriving (Confunctor)

instance Confunctor p => Contravariant (Confunctorially p a) where
  contramap = mapr
