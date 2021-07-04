{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
module Sequoia.Polarity
( -- * Polarities
  N(..)
, P(..)
  -- * Polarization
, Polarized
, Neg
, Pos
) where

import Data.Functor.Identity
import Data.Kind (Type)

-- Polarities

newtype N a = N { getN :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity

newtype P a = P { getP :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity


-- Polarization

class Polarized (p :: Type -> Type) c | c -> p

instance Polarized N (N a)
instance Polarized P (P a)

type Neg = Polarized N
type Pos = Polarized P
