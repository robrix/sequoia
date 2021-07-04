module Sequoia.Connective.Negate
( -- * Negate
  type (-)(..)
) where

import Sequoia.Continuation
import Sequoia.Polarity

newtype k -a = Negate { getNegate :: k a }
  deriving (Applicative, Representable, Contravariant, Functor)

instance Neg a => Polarized P (k -a) where

infixr 9 -
