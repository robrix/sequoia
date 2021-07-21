{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Connective.True
( -- * True
  True(..)
, type (✓)
) where

import Prelude hiding (True)
import Sequoia.Functor.K
import Sequoia.Polarity

-- True

data True r a = True { trueA :: a, trueK :: K r r }
  deriving (Functor)

instance Pos a => Polarized P (True e a)

type (✓) = True

infixr 9 ✓
