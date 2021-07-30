module Sequoia.Connective.Negate
( -- * Negate
  Negate(..)
, type (-)
  -- * Elimination
, (•-)
) where

import Data.Functor.Contravariant
import Data.Profunctor
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Negate

newtype Negate r a = Negate { getNegate :: a • r }

instance Contravariant (Negate r) where
  contramap f = Negate . lmap f . getNegate

instance Neg a => Polarized P (Negate r a) where


type (-) = Negate

infixr 9 -


-- Elimination

(•-) :: Negate r a -> (a -> r)
(•-) = (•) . getNegate

infixl 7 •-
