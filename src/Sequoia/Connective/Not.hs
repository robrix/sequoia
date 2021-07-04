module Sequoia.Connective.Not
( -- * Not
  type (¬)(..)
) where

import Sequoia.Continuation
import Sequoia.Polarity

newtype k ¬a = Not { getNot :: k a }
  deriving (Applicative, Representable, Contravariant, Functor)

instance Pos a => Polarized N (k ¬a) where

infixr 9 ¬
