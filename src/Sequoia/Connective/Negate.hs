module Sequoia.Connective.Negate
( -- * Negate
  Negate(negateE, negateK)
, type (-)
  -- * Construction
, negate
  -- * Elimination
, withNegate
, (•-)
) where

import Data.Functor.Contravariant
import Data.Profunctor
import Prelude hiding (negate)
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Negate

data Negate e r a = Negate { negateE :: e, negateK :: a • r }

instance Contravariant (Negate e r) where
  contramap f (Negate e k) = Negate e (lmap f k)

instance Neg a => Polarized P (Negate e r a) where


type (-) = Negate

infixr 9 -


-- Construction

negate :: e -> a • r -> Negate e r a
negate = Negate


-- Elimination

withNegate :: Negate e r a -> ((e -> a • r -> x) -> x)
withNegate (Negate e k) f = f e k


(•-) :: Negate e r a -> (a -> r)
(•-) = (•) . negateK

infixl 7 •-
