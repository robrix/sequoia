{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Connective.Assertion
( -- * Yes
  Yes(..)
) where

import Data.Distributive
import Sequoia.Functor.V
import Sequoia.Polarity
import Sequoia.Value

-- Yes

newtype Yes e a = Yes { getYes :: V e a }
  deriving (Functor, Representable, Value)

instance Distributive (Yes e) where
  distribute = Yes . distribute . fmap getYes

instance Pos a => Polarized P (Yes e a) where
