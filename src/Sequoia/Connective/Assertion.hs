{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Connective.Assertion
( -- * NotNo
  NotNo(..)
  -- * Yes
, Yes(..)
) where

import Data.Distributive
import Sequoia.Functor.V
import Sequoia.Polarity
import Sequoia.Value as V

-- NotNo

newtype NotNo r a = NotNo { runNotNo :: (a -> r) -> r }


-- Yes

newtype Yes e a = Yes { getYes :: V e a }
  deriving (Functor, V.Representable, Value)

instance Distributive (Yes e) where
  distribute = Yes . distribute . fmap getYes

instance Pos a => Polarized P (Yes e a) where
