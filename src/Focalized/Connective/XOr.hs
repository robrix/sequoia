module Focalized.Connective.XOr
( -- * Exclusive disjunction
  XOr(..)
, type (</)
, type (/>)
, exxor
) where

import Focalized.CPS
import Focalized.Polarity

-- Exclusive disjunction

data XOr r a b
  = XOrL a (r •b)
  | XOrR b (r •a)

instance (Pos a, Pos b) => Polarized P (XOr r a b)

type a </r = XOr r a
type r/> b = r b

infixr 6 </
infixr 5 />

exxor :: (a -> r •b -> c) -> (b -> r •a -> c) -> ((a </r/> b) -> c)
exxor f g = \case
  XOrL a kb -> f a kb
  XOrR b ka -> g b ka
