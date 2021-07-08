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

instance Profunctor (K f) where
  dimap f _ = K . lmap f . runK

instance Strong (K f) where
  first'  = K . lmap fst . runK
  second' = K . lmap snd . runK

instance Cochoice (K f) where
  unleft  = K . lmap Left  . runK
  unright = K . lmap Right . runK

instance Sieve (K f) (Const f) where
  sieve = fmap Const . runK

instance Pro.Representable (K f) where
  type Rep (K f) = Const f
  tabulate = K . fmap getConst
