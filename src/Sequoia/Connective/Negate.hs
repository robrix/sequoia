module Sequoia.Connective.Negate
( -- * Negate
  Negate(..)
, type (-)
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

instance ContinuationE (Negate e) where
  (•) = (•) . negateK

instance Neg a => Polarized P (Negate e a r) where


type (-) = Negate

infixr 9 -


-- Elimination

(•-) :: Negate e a r -> (a -> r)
(•-) = (•) . negateK

infixl 7 •-
