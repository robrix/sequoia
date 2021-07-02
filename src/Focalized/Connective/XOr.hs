module Focalized.Connective.XOr
( -- * Exclusive disjunction
  XOr(..)
) where

import Focalized.CPS

-- Exclusive disjunction

data XOr r a b
  = XOrL a (r •b)
  | XOrR b (r •a)
