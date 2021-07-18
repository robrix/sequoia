{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Polarity
( -- * Polarities
  N(..)
, P(..)
  -- * Polarization
, Polarized
, Neg
, Pos
) where

import Data.Distributive
import Data.Functor.Adjunction as Co
import Data.Functor.Identity
import Data.Functor.Rep as Co
import Data.Kind (Type)

-- Polarities

newtype N a = N { getN :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad, Co.Representable) via Identity

instance Distributive N where
  distribute = N . fmap getN

instance Co.Adjunction N P where
  unit   =    P .    N
  counit = getP . getN
  leftAdjunct  f a =    P (f (   N a))
  rightAdjunct f a = getP (f (getN a))

newtype P a = P { getP :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad, Co.Representable) via Identity

instance Distributive P where
  distribute = P . fmap getP

instance Co.Adjunction P N where
  unit   =    N .    P
  counit = getN . getP
  leftAdjunct  f a =    N (f (   P a))
  rightAdjunct f a = getN (f (getP a))


-- Polarization

class Polarized (p :: Type -> Type) c | c -> p

instance Polarized N (N a)
instance Polarized P (P a)

type Neg = Polarized N
type Pos = Polarized P
