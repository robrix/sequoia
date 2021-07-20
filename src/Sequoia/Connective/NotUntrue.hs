module Sequoia.Connective.NotUntrue
( -- * NotUntrue
  notUntrue
, NotUntrue(..)
, type (≁)
) where

import Data.Functor.Contravariant
import Sequoia.Continuation
import Sequoia.Functor.K
import Sequoia.Polarity

-- NotUntrue

notUntrue :: (e -> a) -> NotUntrue e r a
notUntrue f = NotUntrue ((. f) . runK)

newtype NotUntrue e r a = NotUntrue { runNotUntrue :: K r a -> (e -> r) }

instance Functor (NotUntrue e r) where
  fmap f = NotUntrue . (. contramap f) . runNotUntrue

instance Applicative (NotUntrue e r) where
  pure = notUntrue . const
  NotUntrue f <*> NotUntrue a = NotUntrue (\ k e -> f (inK (\ f -> a (inK (exK k . f)) e)) e)

instance Monad (NotUntrue e r) where
  m >>= f = NotUntrue (\ k e -> runNotUntrue m (inK (\ a -> runNotUntrue (f a) k e)) e)

instance Neg a => Polarized P (NotUntrue e r a)

type (≁) = NotUntrue

infixr 9 ≁
