module Focalized.Snoc
( Snoc(..)
) where

import Data.Foldable (toList)

data Snoc a
  = Nil
  | Snoc a :> a
  deriving (Eq, Foldable, Functor, Ord, Traversable)

infixl 5 :>

instance Show a => Show (Snoc a) where
  showsPrec p s = showParen (p > 10) $ showList (toList s)

instance Semigroup (Snoc a) where
  a <> Nil       = a
  a <> (bs :> b) = (a <> bs) :> b

instance Monoid (Snoc a) where
  mempty = Nil

instance Applicative Snoc where
  pure a = Nil :> a

  Nil     <*> _ = Nil
  fs :> f <*> a = (fs <*> a) <> (f <$> a)
