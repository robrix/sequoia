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

newtype V s a b = V { runV :: s -> b }
  deriving (Applicative, Functor, Monad, Representable)

instance Distributive (V s a) where
  distribute r = V (\ s -> (`runV` s)     <$> r)
  collect  f r = V (\ s -> (`runV` s) . f <$> r)

instance Profunctor (V s) where
  dimap _ g = V . rmap g . runV

instance Costrong (V s) where
  unfirst  = V . fmap fst . runV
  unsecond = V . fmap snd . runV

instance Choice (V s) where
  left'  = V . fmap Left  . runV
  right' = V . fmap Right . runV

instance Closed (V s) where
  closed = V . fmap const . runV

instance Sieve (V s) ((->) s) where
  sieve = const . runV

instance Cosieve (V s) (Const s) where
  cosieve = lmap getConst . runV

instance Pro.Corepresentable (V s) where
  type Corep (V s) = Const s
  cotabulate = V . lmap Const
