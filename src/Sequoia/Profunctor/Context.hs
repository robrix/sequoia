module Sequoia.Profunctor.Context
( C(..)
) where

import Data.Distributive

newtype C e r = C { runC :: e -> r }
  deriving (Applicative, Functor, Monad)

instance Distributive (C e) where
  distribute r = C (\ e -> (`runC` e) <$> r)
