module Sequoia.Connective.NotUntrue
( -- * NotUntrue
  NotUntrue(..)
, type (≁)
  -- * Elimination
, (∘≁)
) where

import Data.Profunctor
import Sequoia.Polarity
import Sequoia.Profunctor.Value

-- NotUntrue

newtype NotUntrue e a = NotUntrue { runNotUntrue :: e ∘ a }
  deriving (Applicative, Functor, Monad, Profunctor)

instance Neg a => Polarized P (NotUntrue e a)

type (≁) = NotUntrue

infixr 9 ≁


-- Elimination

(∘≁) :: e -> e ≁ a -> a
(∘≁) = (. runNotUntrue) . (∘)

infixl 8 ∘≁
