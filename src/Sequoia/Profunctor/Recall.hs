{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Recall
( Recall(..)
) where

import Data.Coerce
import Data.Distributive
import Data.Functor.Rep
import Data.Profunctor

newtype Recall e a b = Recall { runRecall :: e -> b }
  deriving (Applicative, Functor, Monad, Representable)

instance Distributive (Recall s a) where
  distribute = distributeRep
  collect = collectRep

instance Profunctor (Recall e) where
  dimap _ g = Recall . fmap g . runRecall
  lmap _ = coerce
  rmap = fmap

instance Costrong (Recall e) where
  unfirst  = Recall . (fst .) . runRecall
  unsecond = Recall . (snd .) . runRecall

instance Choice (Recall e) where
  left'  = Recall . (Left  .) . runRecall
  right' = Recall . (Right .) . runRecall
