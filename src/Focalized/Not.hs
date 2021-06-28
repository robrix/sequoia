module Focalized.Not
( -- * Not
  runNot
, type (¬)(..)
) where

import Focalized.CPS
import Focalized.Polarity

runNot :: r ¬a -> (a -> r)
runNot = runK . getNot

newtype r ¬a = Not { getNot :: r •a }

instance Pos a => Polarized N (r ¬a) where

infixr 9 ¬
