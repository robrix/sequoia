{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Adjunction
( Adjunction(..)
, cosieveAdjunction
, cotabulateAdjunction
, Coadjunction(..)
, sieveCoadjunction
, tabulateCoadjunction
  -- * Composition
, Adjoint(..)
, Coadjoint(..)
, Boring(..)
, Coboring(..)
) where

import           Control.Comonad
import qualified Data.Functor.Adjunction as Co
import           Data.Functor.Const
import qualified Data.Functor.Rep as Co
import           Data.Profunctor
import qualified Data.Profunctor.Rep as Pro
import           Data.Profunctor.Sieve

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

instance Coadjunction (->) (->) where
  leftCounit  = flip ($)
  rightCounit = flip ($)
  leftCoadjunct  = flip
  rightCoadjunct = flip


sieveCoadjunction :: Coadjunction f u => u a b -> (a -> f c b)
sieveCoadjunction = rightCoadjunct . const

tabulateCoadjunction :: Coadjunction f u => (a -> f () b) -> u a b
tabulateCoadjunction f = leftCoadjunct f ()


newtype Adjoint f u a b = Adjoint { runAdjoint :: u a (f a b) }

instance (Profunctor f, Profunctor u) => Profunctor (Adjoint f u) where
  dimap f g = Adjoint . dimap f (dimap f g) . runAdjoint

instance (Profunctor f, Profunctor u) => Functor (Adjoint f u a) where
  fmap = rmap

instance Adjunction f u => Applicative (Adjoint f u a) where
  pure = Adjoint . leftUnit
  Adjoint f <*> a = Adjoint (rmap (rightAdjunct (runAdjoint . (<$> a))) f)

instance Adjunction f u => Monad (Adjoint f u a) where
  Adjoint u >>= f = Adjoint (rmap (rightAdjunct (runAdjoint . f)) u)

instance Adjunction f u => Comonad (Adjoint u f a) where
  extract = rightUnit . runAdjoint
  extend f = Adjoint . rmap (leftAdjunct (f . Adjoint)) . runAdjoint
  duplicate = Adjoint . rmap (leftAdjunct Adjoint) . runAdjoint


newtype Coadjoint f u a b = Coadjoint { runCoadjoint :: u (f b a) b }

instance (Profunctor f, Profunctor u) => Profunctor (Coadjoint f u) where
  dimap f g = Coadjoint . dimap (dimap g f) g . runCoadjoint

instance (Profunctor f, Profunctor u) => Functor (Coadjoint f u a) where
  fmap = rmap


newtype Boring f a b = Boring { runBoring :: f b }

instance Functor f => Profunctor (Boring f) where
  dimap _ g = Boring . fmap g . runBoring

instance Functor f => Costrong (Boring f) where
  unfirst  = Boring . fmap fst . runBoring
  unsecond = Boring . fmap snd . runBoring

instance Functor f => Choice (Boring f) where
  left'  = Boring . fmap Left  . runBoring
  right' = Boring . fmap Right . runBoring

instance Functor f => Sieve (Boring f) f where
  sieve = const . runBoring

instance (Co.Representable f, Co.Rep f ~ r) => Cosieve (Boring f) (Const r) where
  cosieve = lmap getConst . Co.index . runBoring

instance Co.Representable f => Pro.Corepresentable (Boring f) where
  type Corep (Boring f) = Const (Co.Rep f)
  cotabulate f = Boring (Co.tabulate (f . Const))

instance Co.Adjunction f u => Adjunction (Boring f) (Boring u) where
  leftAdjunct  f a = Boring (Co.leftAdjunct (f . Boring) a)
  rightAdjunct f a = Co.rightAdjunct (runBoring . f) (runBoring a)


newtype Coboring f a b = Coboring { runCoboring :: f a }
