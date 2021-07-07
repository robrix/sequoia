{-# LANGUAGE TypeFamilies #-}
module Sequoia.Functor.I
( -- Identity functor
  I(..)
) where

import Control.Applicative (liftA2)
import Control.Comonad
import Data.Coerce
import Data.Distributive
import Data.Functor.Adjunction
import Data.Functor.Rep

newtype I a = I { getI :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative I where
  pure = coerce
  liftA2 = coerce
  (<*>) = coerce

instance Monad I where
  (>>=) = flip coerce

instance Comonad I where
  extract = coerce
  extend = coerce

instance Distributive I where
  distribute = I . fmap  getI
  collect f  = I . fmap (getI . f)

instance Representable I where
  type Rep I = ()
  tabulate = I . ($ ())
  index = const . getI

instance Adjunction I I where
  unit   = coerce
  counit = coerce
  leftAdjunct  = coerce
  rightAdjunct = coerce
