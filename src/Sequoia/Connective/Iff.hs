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

newtype Iff e r a b = Iff { getIff :: (Down a ~~Fun r~> b) & (Down b ~~Fun r~> a) }

instance (Neg a, Neg b) => Polarized N (Iff e r a b)

type a <~(r :: Type -> Type -> Type) = r a

infixr 6 <~
