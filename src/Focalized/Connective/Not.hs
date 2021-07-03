module Focalized.Connective.Not
( -- * Not
  type (¬)(..)
) where

import Data.Functor.Contravariant
import Focalized.Continuation
import Focalized.Polarity

newtype k ¬a = Not { getNot :: k a }
  deriving (Applicative, Contrapplicative, Contravariant, Functor)

instance Pos a => Polarized N (k ¬a) where

infixr 9 ¬
