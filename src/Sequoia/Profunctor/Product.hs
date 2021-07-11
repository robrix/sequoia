module Sequoia.Profunctor.Product
( (:*:)(..)
) where

import Control.Arrow ((***))
import Data.Profunctor

newtype (p :*: q) a b = Product { runProduct :: (p a b, q a b) }

infixr 6 :*:

instance (Profunctor p, Profunctor q) => Profunctor (p :*: q) where
  dimap f g = Product . (dimap f g *** dimap f g) . runProduct

instance (Strong p, Strong q) => Strong (p :*: q) where
  first'  = Product . (first'  *** first')  . runProduct
  second' = Product . (second' *** second') . runProduct

instance (Choice p, Choice q) => Choice (p :*: q) where
  left'  = Product . (left'  *** left')  . runProduct
  right' = Product . (right' *** right') . runProduct
