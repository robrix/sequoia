module Sequoia.Profunctor.Exchange
( Exchange(..)
) where

import Data.Profunctor

data Exchange a b s t = Exchange (s -> a) (b -> t)
  deriving (Functor)

instance Profunctor (Exchange a b) where
  dimap f g (Exchange sa bt) = Exchange (sa . f) (g . bt)
