module Sequoia.Connective.Negate
( -- * Negate
  Negate
, type (-)
  -- * Construction
, negate
  -- * Elimination
, withNegate
, negateE
, negateK
, (•-)
) where

import Data.Functor.Contravariant
import Data.Profunctor
import Prelude hiding (negate)
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Negate

data Negate e r a = Negate e (a • r)

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


negateE :: Negate e r a -> e
negateE n = withNegate n const

negateK :: Negate e r a -> a • r
negateK n = withNegate n (const id)


(•-) :: Negate e r a -> (a -> r)
(•-) = (•) . negateK

infixl 7 •-
