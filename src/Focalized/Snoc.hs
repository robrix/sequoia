module Focalized.Snoc
( Snoc(..)
, lookup
) where

import Control.Applicative
import Data.Foldable (toList)
import Prelude hiding (lookup)

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

instance Alternative Snoc where
  empty = Nil
  (<|>) = (<>)

instance Monad Snoc where
  Nil >>= _     = Nil
  as :> a >>= f = (as >>= f) <> f a


lookup :: Eq a => a -> Snoc (a, b) -> Maybe b
lookup a = go
  where
  go Nil = Nothing
  go (as :> (a', b))
    | a == a'   = Just b
    | otherwise = go as
