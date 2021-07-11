module Sequoia.Profunctor.Product
( (:*:)(..)
) where

import Control.Arrow ((***))
import Data.Profunctor

newtype (p :*: q) a b = Product { runProduct :: (p a b, q a b) }

infixr 6 :*:

instance (Profunctor p, Profunctor q) => Profunctor (p :*: q) where
  dimap f g = Product . (dimap f g *** dimap f g) . runProduct
