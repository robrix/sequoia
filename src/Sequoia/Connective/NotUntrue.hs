module Sequoia.Connective.NotUntrue
( -- * NotUntrue
  NotUntrue(..)
, type (≁)
) where

import Data.Profunctor
import Sequoia.Polarity
import Sequoia.Profunctor.Value

-- NotUntrue

newtype NotUntrue e a = NotUntrue { runNotUntrue :: e ∘ a }
  deriving (Applicative, Functor, Monad, Profunctor, Value)

instance Neg a => Polarized P (NotUntrue e a)

type (≁) = NotUntrue

infixr 9 ≁
