module Sequoia.Snoc
( -- Snoc lists
  Snoc(..)
) where

import Data.Align
import Data.Foldable (toList)
import Data.These
import Data.Zip

-- Snoc lists

data Snoc a
  = Nil
  | Snoc a :> a
  deriving (Eq, Foldable, Functor, Ord, Traversable)

infixl 5 :>

instance Show a => Show (Snoc a) where
  showsPrec p s = showParen (p > 10) $ showString "fromList" . showChar ' ' . showList (toList s)

instance Semigroup (Snoc a) where
  a <> b = go id b
    where
    go acc = \case
      Nil   -> acc a
      bs:>b -> go (acc . (:> b)) bs

instance Monoid (Snoc a) where
  mempty = Nil

instance Semialign Snoc where
  align = go id
    where
    go acc = curry $ \case
      (Nil, Nil)     -> acc Nil
      (Nil, bs)      -> acc (That <$> bs)
      (as,  Nil)     -> acc (This <$> as)
      (as:>a, bs:>b) -> go (acc . (:> These a b)) as bs

instance Zip Snoc where
  zipWith f = go id
    where
    go acc = curry $ \case
      (as:>a, bs:>b) -> go (acc . (:> f a b)) as bs
      _              -> acc Nil
