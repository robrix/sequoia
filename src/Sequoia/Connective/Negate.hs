module Sequoia.Connective.Negate
( -- * Negate
  Negate(..)
, type (-)
  -- * Construction
, negate
  -- * Elimination
, negateE
, negateK
, (•-)
) where

import Data.Profunctor
import Prelude hiding (negate)
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Negate

newtype Negate e a r = Negate { withNegate :: forall x . (e -> a • r -> x) -> x }
  deriving (Functor)

instance Profunctor (Negate e) where
  dimap f g n = withNegate n $ \ e k -> negate e (dimap f g k)

instance Neg a => Polarized P (Negate e a r) where


type (-) = Negate

infixr 9 -


-- Construction

negate :: e -> a • r -> Negate e a r
negate e k = Negate (\ f -> f e k)


-- Elimination

negateE :: Negate e a r -> e
negateE n = withNegate n const

negateK :: Negate e a r -> a • r
negateK n = withNegate n (const id)


(•-) :: Negate e a r -> (a -> r)
(•-) = (•) . negateK

infixl 7 •-
