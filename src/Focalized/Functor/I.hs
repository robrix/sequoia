module Focalized.Functor.I
( -- Identity functor
  I(..)
) where

newtype I a = I { getI :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
