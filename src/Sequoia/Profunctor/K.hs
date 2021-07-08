{-# LANGUAGE TypeFamilies #-}
module Sequoia.Profunctor.K
( K(..)
) where

import           Data.Functor.Const
import           Data.Profunctor
import qualified Data.Profunctor.Rep as Pro
import           Data.Profunctor.Sieve

newtype K r a b = K { runK :: a -> r }
  deriving (Functor)

instance Profunctor (K r) where
  dimap f _ = K . lmap f . runK

instance Strong (K r) where
  first'  = K . lmap fst . runK
  second' = K . lmap snd . runK

instance Cochoice (K r) where
  unleft  = K . lmap Left  . runK
  unright = K . lmap Right . runK

instance Sieve (K r) (Const r) where
  sieve = fmap Const . runK

instance Pro.Representable (K r) where
  type Rep (K r) = Const r
  tabulate = K . fmap getConst
