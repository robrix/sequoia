module Focalized.Continuation
( -- * Continuations
  type (•)(..)
) where

import qualified Control.Category as Cat
import           Data.Functor.Contravariant

-- Continuations

newtype r •a = K { (•) :: a -> r }

infixl 9 •

instance Cat.Category (•) where
  id = K id
  K f . K g = K (g . f)

instance Contravariant ((•) r) where
  contramap f = K . (. f) . (•)
