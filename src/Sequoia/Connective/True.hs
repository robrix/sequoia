{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Connective.True
( -- * True
  True(..)
, type (✓)
  -- * Construction
, true
) where

import Prelude hiding (True)
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- True

data True r a = True { trueA :: a, trueK :: r • r }
  deriving (Functor)

instance Pos a => Polarized P (True e a)

type (✓) = True

infixr 9 ✓


-- Construction

true :: a -> True r a
true = (`True` idK)
