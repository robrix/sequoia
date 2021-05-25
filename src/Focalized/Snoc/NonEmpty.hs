module Focalized.Snoc.NonEmpty
( NonEmpty(..)
) where

import Focalized.Snoc

data NonEmpty a = Snoc a :|> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixl 5 :|>
