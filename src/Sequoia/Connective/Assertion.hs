{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Connective.Assertion
( -- * NotNo
  NotNo(..)
  -- * True
, True(..)
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

instance Neg a => Polarized P (NotNo r a)


-- True

newtype True e a = True' { getTrue :: V e a }
  deriving (Applicative, Functor, Monad, V.Representable, Value)

instance Distributive (True e) where
  distribute = True' . distribute . fmap getTrue

instance Pos a => Polarized P (True e a)
