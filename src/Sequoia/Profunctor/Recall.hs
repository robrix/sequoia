{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Recall
( Recall(..)
) where

import Data.Distributive
import Data.Functor.Rep

newtype Recall e a b = Recall { runRecall :: e -> b }
  deriving (Applicative, Functor, Monad, Representable)

instance Distributive (Recall s a) where
  distribute = distributeRep
  collect = collectRep
