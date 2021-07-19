{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Recall
( Recall(..)
) where

import Data.Coerce
import Data.Distributive
import Data.Functor.Const
import Data.Functor.Rep as Co
import Data.Profunctor
import Data.Profunctor.Rep as Pro
import Data.Profunctor.Sieve

newtype Recall e a b = Recall { runRecall :: e -> b }
  deriving (Applicative, Functor, Monad, Co.Representable)

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

instance Closed (Recall e) where
  closed = Recall . (const .) . runRecall

instance Sieve (Recall e) ((->) e) where
  sieve = const . runRecall

instance Cosieve (Recall e) (Const e) where
  cosieve = (. getConst) . runRecall

instance Pro.Corepresentable (Recall e) where
  type Corep (Recall e) = Const e
  cotabulate = Recall . (. Const)
