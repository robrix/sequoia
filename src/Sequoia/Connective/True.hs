{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Connective.True
( -- * True
  true
, True(..)
, type (✓)
) where

import Prelude hiding (True)
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- True

true :: a -> True r a
true = (`True` K id)

data True r a = True { trueA :: a, trueK :: K r r }
  deriving (Functor)

instance Pos a => Polarized P (True e a)

type (✓) = True

infixr 9 ✓
