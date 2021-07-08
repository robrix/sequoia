{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.V
( V(..)
) where

import           Data.Distributive
import           Data.Functor.Const
import           Data.Functor.Rep
import           Data.Profunctor
import qualified Data.Profunctor.Rep as Pro
import           Data.Profunctor.Sieve

newtype V f s a b = V { runV :: f s -> b }
  deriving (Applicative, Functor, Monad, Representable)

instance Distributive (V f s a) where
  distribute r = V (\ s -> (`runV` s)     <$> r)
  collect  f r = V (\ s -> (`runV` s) . f <$> r)

instance Profunctor (V f s) where
  dimap _ g = V . rmap g . runV

instance Costrong (V f s) where
  unfirst  = V . fmap fst . runV
  unsecond = V . fmap snd . runV

instance Choice (V f s) where
  left'  = V . fmap Left  . runV
  right' = V . fmap Right . runV

instance Closed (V f s) where
  closed = V . fmap const . runV

instance Sieve (V f s) ((->) (f s)) where
  sieve = const . runV

instance Cosieve (V f s) (Const (f s)) where
  cosieve = lmap getConst . runV

instance Pro.Corepresentable (V f s) where
  type Corep (V f s) = Const (f s)
  cotabulate = V . lmap Const
