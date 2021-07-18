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
  deriving (Functor)

instance Applicative (NotNo r) where
  pure a = NotNo ($ a)
  NotNo f <*> NotNo a = NotNo (f . (a .) . (.))

instance Monad (NotNo r) where
  m >>= f = NotNo (\ k -> runNotNo m ((`runNotNo` k) . f))


-- Yes

newtype Yes e a = Yes { getYes :: V e a }
  deriving (Applicative, Functor, Monad, V.Representable, Value)

instance Distributive (Yes e) where
  distribute = Yes . distribute . fmap getYes

instance Pos a => Polarized P (Yes e a)
