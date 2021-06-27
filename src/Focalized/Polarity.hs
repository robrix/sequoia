module Focalized.Polarity
( -- * Polarities
  N(..)
, P(..)
) where

-- Polarities

import Data.Functor.Identity

newtype N a = N { getN :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity

newtype P a = P { getP :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity
