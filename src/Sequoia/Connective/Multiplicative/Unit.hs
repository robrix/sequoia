{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Connective.Multiplicative.Unit
( -- * Negative falsity
  Bottom(..)
  -- ** Elimination
, absurdNK
  -- * Positive truth
, One(..)
) where

import Data.Distributive
import Data.Functor.Adjunction
import Data.Functor.Identity
import Data.Functor.Rep
import Sequoia.Nulladjunction
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Adjunction

instance Adjunction Bottom One where
  leftAdjunct  f = One . f . Bottom
  rightAdjunct f = getOne . f . absurdN

instance Adjunction One Bottom where
  leftAdjunct  f = Bottom . f . One
  rightAdjunct f = absurdN . f . getOne

instance Nulladjunction r e => Nulladjunction (Bottom r) (One e) where
  nullleftAdjunct f = One . nullleftAdjunct (f . Bottom)
  nullrightAdjunct f = nullrightAdjunct (getOne . f) . absurdN

instance Nulladjunction e r => Nulladjunction (One e) (Bottom r) where
  nullleftAdjunct f = Bottom . nullleftAdjunct (f . One)
  nullrightAdjunct f = nullrightAdjunct (absurdN . f) . getOne


-- Negative falsity

newtype Bottom r = Bottom { absurdN :: r }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad, Representable) via Identity

instance Polarized N (Bottom r) where

instance Distributive Bottom where
  distribute = Bottom . fmap absurdN
  collect f = Bottom . fmap (absurdN . f)


-- Elimination

absurdNK :: Continuation k => Bottom r `k` r
absurdNK = inK absurdN


-- Positive truth

newtype One e = One { getOne :: e }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad, Representable) via Identity

instance Polarized P (One e) where

instance Distributive One where
  distribute = One . fmap getOne
  collect f = One . fmap (getOne . f)
