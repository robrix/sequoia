module Sequoia.Connective.NotUntrue
( -- * NotUntrue
  notUntrue
, NotUntrue(..)
, type (≁)
) where

import Sequoia.Polarity

-- NotUntrue

notUntrue :: (e -> a) -> NotUntrue e r a
notUntrue f = NotUntrue (. f)

newtype NotUntrue e r a = NotUntrue { runNotUntrue :: (a -> r) -> (e -> r) }
  deriving (Functor)

instance Applicative (NotUntrue e r) where
  pure = notUntrue . const
  NotUntrue f <*> NotUntrue a = NotUntrue (\ k e -> f (\ f -> a (k . f) e) e)

instance Monad (NotUntrue e r) where
  m >>= f = NotUntrue (\ k e -> runNotUntrue m (\ a -> runNotUntrue (f a) k e) e)

instance Neg a => Polarized P (NotUntrue e r a)

type (≁) = NotUntrue

infixr 9 ≁
