module Sequoia.Connective.Negate
( -- * Negate
  Negate(..)
, type (-)
  -- * Construction
, negate
  -- * Elimination
, (•-)
) where

import Data.Profunctor
import Prelude hiding (negate)
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Negate

data Negate e a r = Negate { negateE :: e, negateK :: a • r }
  deriving (Functor)

instance Profunctor (Negate e) where
  dimap f g (Negate e k) = Negate e (dimap f g k)

instance Neg a => Polarized P (Negate e a r) where


type (-) = Negate

infixr 9 -


-- Construction

negate :: e -> a • r -> Negate e a r
negate = Negate


-- Elimination

(•-) :: Negate e a r -> (a -> r)
(•-) = (•) . negateK

infixl 7 •-
