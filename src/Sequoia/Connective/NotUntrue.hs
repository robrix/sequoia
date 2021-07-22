module Sequoia.Connective.NotUntrue
( -- * NotUntrue
  notUntrue
, NotUntrue(..)
, type (≁)
) where

import Sequoia.Functor.Source
import Sequoia.Polarity
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Continuation

-- NotUntrue

notUntrue :: (e -> a) -> NotUntrue e r a
notUntrue f = NotUntrue (Src (C . (. f) . (•)))

newtype NotUntrue e r a = NotUntrue { runNotUntrue :: Src e r a }
  deriving (Applicative, Functor, Monad)

instance Neg a => Polarized P (NotUntrue e r a)

type (≁) = NotUntrue

infixr 9 ≁
