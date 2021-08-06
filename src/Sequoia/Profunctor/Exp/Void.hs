module Sequoia.Profunctor.Exp.Void
( -- * Exponentials
  type (-->)(..)
  -- * Coexponentials
, type (>--)(..)
) where

import Data.Void

-- Exponentials

newtype a --> b = Exp { getExp :: (b -> Void) -> (a -> Void) }
  deriving (Functor)

infixr 0 -->


-- Coexponentials

data b >-- a = (:>--) { coreturn :: b -> Void, coconst :: a }
  deriving (Functor)

infixr 0 >--, :>--
