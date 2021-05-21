module Focalized.B
( B(..)
) where

data B a
  = Nil
  | Leaf a
  | B a :<>: B a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 5 :<>:

instance Semigroup (B a) where
  (<>) = (:<>:)

instance Monoid (B a) where
  mempty = Nil
