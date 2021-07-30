module Sequoia.Connective.Not
( -- * Not
  Not(..)
, type (¬)
  -- * Elimination
, (•¬)
) where

import Data.Functor.Contravariant
import Data.Profunctor
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Not

newtype Not r a = Not { getNot :: a • r }

instance Contravariant (Not r) where
  contramap f = Not . lmap f . getNot

instance Pos a => Polarized N (Not r a) where


type (¬) = Not

infixr 9 ¬


-- Elimination

(•¬) :: Not r a -> (a -> r)
(•¬) = (•) . getNot

infixl 7 •¬
