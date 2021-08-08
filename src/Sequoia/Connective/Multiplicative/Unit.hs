{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Connective.Multiplicative.Unit
( -- * Negative falsity
  Bottom(..)
  -- * Positive truth
, One(..)
) where

import Data.Distributive
import Data.Functor.Adjunction
import Data.Functor.Identity
import Data.Functor.Rep
import Sequoia.Nulladjunction
import Sequoia.Polarity

-- Adjunction

instance Adjunction Bottom One where
  leftAdjunct  f = One . f . Bottom
  rightAdjunct f = getOne . f . absurdN

instance Nulladjunction r e => Nulladjunction (Bottom r) (One e) where
  nullleftAdjunct f = One . nullleftAdjunct (f . Bottom)
  nullrightAdjunct f = nullrightAdjunct (getOne . f) . absurdN


-- Negative falsity

newtype Bottom r = Bottom { absurdN :: r }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad, Representable) via Identity

instance Polarized N (Bottom r) where

instance Distributive Bottom where
  distribute = Bottom . fmap absurdN
  collect f = Bottom . fmap (absurdN . f)


-- Positive truth

newtype One e = One { getOne :: e }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad, Representable) via Identity

instance Polarized P (One e) where

instance Distributive One where
  distribute = One . fmap getOne
  collect f = One . fmap (getOne . f)
