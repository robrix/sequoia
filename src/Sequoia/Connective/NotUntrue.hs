module Sequoia.Connective.NotUntrue
( -- * NotUntrue
  notUntrue
, NotUntrue(..)
, type (≁)
) where

import Sequoia.Polarity

-- NotUntrue

notUntrue :: a -> NotUntrue r a
notUntrue a = NotUntrue ($ a)

newtype NotUntrue r a = NotUntrue { runNotUntrue :: (a -> r) -> r }
  deriving (Functor)

instance Applicative (NotUntrue r) where
  pure a = NotUntrue ($ a)
  NotUntrue f <*> NotUntrue a = NotUntrue (f . (a .) . (.))

instance Monad (NotUntrue r) where
  m >>= f = NotUntrue (\ k -> runNotUntrue m ((`runNotUntrue` k) . f))

instance Neg a => Polarized P (NotUntrue r a)

type (≁) = NotUntrue

infixr 9 ≁
