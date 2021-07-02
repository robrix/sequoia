module Focalized.Connective.Not
( -- * Not
  runNot
, appNot
, type (¬)(..)
) where

import Focalized.CPS
import Focalized.Polarity

runNot :: r ¬a -> (a -> r)
runNot = (•) . getNot

appNot :: a -> r ¬a -> r
appNot = flip runNot

newtype r ¬a = Not { getNot :: r •a }

instance Pos a => Polarized N (r ¬a) where

infixr 9 ¬
