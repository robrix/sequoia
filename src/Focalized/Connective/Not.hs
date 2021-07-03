module Focalized.Connective.Not
( -- * Not
  type (¬)(..)
) where

import Focalized.Polarity

newtype k ¬a = Not { getNot :: k a }

instance Pos a => Polarized N (k ¬a) where

infixr 9 ¬
