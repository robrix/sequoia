module Focalized.Connective.Negate
( -- * Negate
  type (-)(..)
) where

import Focalized.Continuation
import Focalized.Polarity

newtype k -a = Negate { getNegate :: k a }
  deriving (Applicative, Representable, Contravariant, Functor)

instance Neg a => Polarized P (k -a) where

infixr 9 -
