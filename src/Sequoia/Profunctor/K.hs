{-# LANGUAGE TypeFamilies #-}
module Sequoia.Profunctor.K
( K(..)
) where

import           Data.Functor.Const
import           Data.Profunctor
import qualified Data.Profunctor.Rep as Pro
import           Data.Profunctor.Sieve

newtype K f r a b = K { runK :: a -> f r }
  deriving (Functor)

instance Profunctor (K f r) where
  dimap f _ = K . lmap f . runK

instance Strong (K f r) where
  first'  = K . lmap fst . runK
  second' = K . lmap snd . runK

instance Cochoice (K f r) where
  unleft  = K . lmap Left  . runK
  unright = K . lmap Right . runK

instance Sieve (K f r) (Const (f r)) where
  sieve = fmap Const . runK

instance Pro.Representable (K f r) where
  type Rep (K f r) = Const (f r)
  tabulate = K . fmap getConst
