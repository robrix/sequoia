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
import Sequoia.Profunctor.Context

-- NotUntrue

notUntrue :: (e -> a) -> NotUntrue e r a
notUntrue f = NotUntrue (C . (. f) . runK)

newtype NotUntrue e r a = NotUntrue { runNotUntrue :: K r a -> C e r }

instance Functor (NotUntrue e r) where
  fmap f = NotUntrue . (. contramap f) . runNotUntrue

instance Applicative (NotUntrue e r) where
  pure = notUntrue . const
  NotUntrue f <*> NotUntrue a = NotUntrue (\ k -> cont (\ _K -> f (_K (\ f -> a (inK (exK k . f))))))

instance Monad (NotUntrue e r) where
  NotUntrue m >>= f = NotUntrue (\ k -> cont (\ _K -> m (_K (\ a -> runNotUntrue (f a) k))))

instance Neg a => Polarized P (NotUntrue e r a)

type (≁) = NotUntrue

infixr 9 ≁
