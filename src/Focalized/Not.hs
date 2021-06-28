module Focalized.Not
( -- * Not
  type (¬)(..)
) where

import Focalized.CPS
import Focalized.Polarity

newtype r ¬a = Not { getNot :: r •a }

instance Pos a => Polarized N (r ¬a) where

infixr 9 ¬
