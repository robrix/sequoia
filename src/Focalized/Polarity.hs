{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
module Focalized.Polarity
( -- * Polarities
  N(..)
, P(..)
  -- * Polarization
, Polarized
, Neg
, Pos
) where

-- Polarities

import Data.Functor.Identity
import Data.Kind (Type)

newtype N a = N { getN :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity

newtype P a = P { getP :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity


class Polarized (p :: Type -> Type) c | c -> p

instance Polarized N (N a)
instance Polarized P (P a)

type Neg = Polarized N
type Pos = Polarized P
