{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Context
( C(..)
) where

import Data.Distributive
import Data.Functor.Rep as Co

newtype C e r = C { runC :: e -> r }
  deriving (Applicative, Functor, Monad, Co.Representable)

instance Distributive (C e) where
  distribute = distributeRep
  collect = collectRep
