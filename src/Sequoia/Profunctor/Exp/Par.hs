module Sequoia.Profunctor.Exp.Par
( -- * Exponentials
  Exp(..)
) where

import Data.Bifunctor (bimap)
import Data.Profunctor
import Sequoia.Calculus.Not
import Sequoia.Calculus.NotUntrue
import Sequoia.Calculus.Par

-- Exponentials

newtype Exp e r a b = Exp { getExp :: a ¬ r ⅋ e ≁ b }
  deriving (Functor)

instance Profunctor (Exp e r) where
  dimap f g = Exp . bimap (lmap f) (rmap g) . getExp
