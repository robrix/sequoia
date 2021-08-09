module Sequoia.Snoc
( -- Snoc lists
  Snoc(..)
) where

import Data.Align
import Data.Foldable (toList)
import Data.These

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

instance Semialign Snoc where
  align Nil     Nil     = Nil
  align Nil     bs      = That <$> bs
  align as      Nil     = This <$> as
  align (as:>a) (bs:>b) = align as bs :> These a b
