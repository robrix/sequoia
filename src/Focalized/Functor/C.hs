{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Functor.C
( type(·)(..)
) where

import Data.Distributive
import Data.Functor.Rep
import Focalized.Polarity

newtype (f · g) a = C { getC :: f (g a) }
  deriving (Eq, Foldable, Functor, Ord, Show)

infixr 7 ·

deriving instance (Traversable f, Traversable g) => Traversable (f · g)

instance Polarized p (f (g a)) => Polarized p ((f · g) a) where

instance (Applicative f, Applicative g) => Applicative (f · g) where
  pure = C . pure . pure
  f <*> a = C ((<*>) <$> getC f <*> getC a)

instance (Distributive f, Distributive g) => Distributive (f · g) where
  distribute r = C (distribute <$> distribute (getC <$> r))
  collect f r = C (distribute <$> distribute (getC . f <$> r))

instance (Representable f, Representable g) => Representable (f · g) where
  type Rep (f · g) = (Rep f, Rep g)
  tabulate = C . tabulate . fmap tabulate . curry
  index    = uncurry . fmap index . index . getC
