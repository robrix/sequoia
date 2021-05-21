module Focalized.B
( B(..)
) where

import Data.Foldable (toList)

data B a
  = Nil
  | Leaf a
  | B a :<>: B a
  deriving (Eq, Foldable, Functor, Ord, Traversable)

infixr 5 :<>:

instance Show a => Show (B a) where
  showsPrec _ = showList . toList

instance Semigroup (B a) where
  (<>) = (:<>:)

instance Monoid (B a) where
  mempty = Nil

instance Applicative B where
  pure = Leaf

  Nil        <*> _ = Nil
  Leaf f     <*> a = f <$> a
  fl :<>: fr <*> a = (fl <*> a) <> (fr <*> a)
