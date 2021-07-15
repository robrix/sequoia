module Sequoia.Connective.Iff
( -- * Logical biconditional
  Iff(..)
, type (<~)
, type (~>)
) where

import Data.Kind (Type)
import Sequoia.Connective.Down
import Sequoia.Connective.Function
import Sequoia.Connective.With
import Sequoia.Polarity

-- Logical biconditional

newtype Iff r e a b = Iff { getIff :: (Down a ~~Fun r e~> b) & (Down b ~~Fun r e~> a) }

instance (Neg a, Neg b) => Polarized N (Iff r e a b)

type a <~(r :: Type -> Type -> Type) = r a

infixr 6 <~
