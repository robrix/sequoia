{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Connective.True
( -- * True
  true
, True(..)
, type (✓)
) where

import Prelude hiding (True)
import Sequoia.Functor.Continuation
import Sequoia.Polarity

-- True

true :: a -> True r a
true = (`True` idK)

data True r a = True { trueA :: a, trueK :: K r r }
  deriving (Functor)

instance Pos a => Polarized P (True e a)

type (✓) = True

infixr 9 ✓
