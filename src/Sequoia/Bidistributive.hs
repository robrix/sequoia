module Sequoia.Bidistributive
( -- * Bidistributive
  Bidistributive(..)
) where

import Data.Bifunctor

class Bifunctor p => Bidistributive p where
  {-# MINIMAL bidistribute | bicollect #-}

  bidistribute :: Functor f => f (p b c) -> p (f b) (f c)
  bidistribute = bicollect id

  bicollect :: Functor f => (a -> p b c) -> f a -> p (f b) (f c)
  bicollect f = bidistribute . fmap f
