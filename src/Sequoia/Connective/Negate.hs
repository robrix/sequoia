module Sequoia.Connective.Negate
( -- * Negate
  Negate(withNegate)
, type (-)
  -- * Construction
, negate
  -- * Elimination
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

newtype Negate e r a = Negate { withNegate :: forall x . (e -> a • r -> x) -> x }

instance Contravariant (Negate e r) where
  contramap f n = withNegate n $ \ e k -> negate e (lmap f k)

instance Neg a => Polarized P (Negate e r a) where


type (-) = Negate

infixr 9 -


-- Construction

negate :: e -> a • r -> Negate e r a
negate e k = Negate (\ f -> f e k)


-- Elimination

negateE :: Negate e r a -> e
negateE n = withNegate n const

negateK :: Negate e r a -> a • r
negateK n = withNegate n (const id)


(•-) :: Negate e r a -> (a -> r)
(•-) = (•) . negateK

infixl 7 •-
