module Sequoia.Snoc
( -- Snoc lists
  Snoc(..)
) where

import Control.Applicative (Alternative(..))
import Data.Align
import Data.Foldable (toList)
import Data.Functor.Classes
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

instance Applicative Snoc where
  pure = (Nil :>)
  fs <*> as = go id fs as
    where
    go accum Nil     _  = accum Nil
    go accum (fs:>f) as = go (accum . flip (foldl (\ fas a -> fas :> f a)) as) fs as

instance Alternative Snoc where
  empty = Nil
  (<|>) = (<>)

instance Monad Snoc where
  as >>= f = go id as
    where
    go accum Nil     = accum Nil
    go accum (as:>a) = go (accum . (<> f a)) as

instance Eq1 Snoc where
  liftEq eq = go
    where
    go Nil      Nil      = True
    go (s1:>a1) (s2:>a2) = eq a1 a2 && go s1 s2
    go _        _        = False

instance Ord1 Snoc where
  liftCompare compare = go
    where
    go Nil      Nil      = EQ
    go (s1:>a1) (s2:>a2) = compare a1 a2 <> go s1 s2
    go Nil      _        = LT
    go _        _        = GT
