module Sequoia.Profunctor.Exp.Void
( -- * Exponentials
  type (-->)(..)
) where

import Data.Void

-- Exponentials

newtype a --> b = Exp { getExp :: (b -> Void) -> (a -> Void) }
  deriving (Functor)

infixr 0 -->
