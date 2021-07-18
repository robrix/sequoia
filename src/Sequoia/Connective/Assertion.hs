{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Connective.Assertion
( -- * NotUntrue
  NotUntrue(..)
  -- * True
, True(..)
, type (✓)
) where

import Data.Distributive
import Prelude hiding (True)
import Sequoia.Functor.V
import Sequoia.Polarity
import Sequoia.Value as V

-- NotUntrue

newtype NotUntrue r a = NotUntrue { runNotUntrue :: (a -> r) -> r }
  deriving (Functor)

instance Applicative (NotUntrue r) where
  pure a = NotUntrue ($ a)
  NotUntrue f <*> NotUntrue a = NotUntrue (f . (a .) . (.))

instance Monad (NotUntrue r) where
  m >>= f = NotUntrue (\ k -> runNotUntrue m ((`runNotUntrue` k) . f))

instance Neg a => Polarized P (NotUntrue r a)


-- True

newtype True e a = True { getTrue :: V e a }
  deriving (Applicative, Functor, Monad, V.Representable, Value)

instance Distributive (True e) where
  distribute = True . distribute . fmap getTrue

instance Pos a => Polarized P (True e a)

type (✓) = True

infixr 9 ✓
