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

newtype Negate e r a = Negate { getNegate :: a • r }

instance Contravariant (Negate e r) where
  contramap f = Negate . lmap f . getNegate

instance Neg a => Polarized P (Negate e r a) where


type (-) = Negate

infixr 9 -


-- Elimination

(•-) :: Negate e r a -> (a -> r)
(•-) = (•) . getNegate

infixl 7 •-
