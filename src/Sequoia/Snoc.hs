module Sequoia.Snoc
( -- Snoc lists
  Snoc(..)
) where

import Data.Foldable (toList)

-- Snoc lists

data Snoc a
  = Nil
  | Snoc a :> a
  deriving (Eq, Foldable, Functor, Ord, Traversable)

infixl 5 :>

instance Show a => Show (Snoc a) where
  showsPrec p s = showParen (p > 10) $ showString "fromList" . showChar ' ' . showList (toList s)

instance Semigroup (Snoc a) where
  a <> Nil       = a
  a <> (bs :> b) = (a <> bs) :> b

instance Monoid (Snoc a) where
  mempty = Nil
