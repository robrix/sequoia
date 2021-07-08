module Sequoia.Connective.Subtraction
( -- * Subtraction
  Sub(..)
, type (~-)
, type (-<)
, sub
) where

import Sequoia.Bijection
import Sequoia.Connective.Negate
import Sequoia.Connective.Tensor
import Sequoia.Polarity

-- Subtraction

data Sub k a b = Sub { subA :: a, subK :: k b () }

instance (Pos a, Neg b) => Polarized P (Sub k a b) where

type a ~-k = Sub k a
type s-< b = s b

infixr 6 ~-
infixr 5 -<


sub :: a ⊗ (k -b) () <-> a ~-k-< b
sub = (\ (a :⊗ k) -> Sub a (getNegate k)) <-> (\ (Sub a k) -> a :⊗ Negate k)
