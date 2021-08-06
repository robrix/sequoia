module Sequoia.Profunctor.Exp.Void
( -- * Exponentials
  type (-->)(..)
  -- * Coexponentials
, type (>--)(..)
) where

import qualified Control.Category as Cat
import           Data.Void

-- Exponentials

newtype a --> b = Exp { getExp :: (b -> Void) -> (a -> Void) }
  deriving (Functor)

infixr 0 -->

instance Cat.Category (-->) where
  id = Exp id
  f . g = Exp (getExp g . getExp f)


-- Coexponentials

data b >-- a = (:>--) { coreturn :: b -> Void, coconst :: a }
  deriving (Functor)

infixr 0 >--, :>--
