{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Connective.True
( -- * True
  True(..)
, type (✓)
) where

import Data.Distributive
import Prelude hiding (True)
import Sequoia.Functor.V
import Sequoia.Polarity
import Sequoia.Value as V

-- True

newtype True e a = True { getTrue :: V e a }
  deriving (Applicative, Functor, Monad, V.Representable, Value)

instance Distributive (True e) where
  distribute = True . distribute . fmap getTrue

instance Pos a => Polarized P (True e a)

type (✓) = True

infixr 9 ✓
