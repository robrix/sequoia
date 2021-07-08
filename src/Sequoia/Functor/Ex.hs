{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
-- | A covariant functor over a profunctor’s output.
module Sequoia.Functor.Ex
( Ex(..)
) where

import Data.Distributive
import Data.Functor.Rep (Representable(..))
import Data.Profunctor
import Data.Profunctor.Rep (Corepresentable(..))
import Data.Profunctor.Sieve

newtype Ex p s a = Ex { runEx :: p s a }
  deriving (Choice, Closed, Cochoice, Costrong, Profunctor, Strong)

instance Profunctor p => Functor (Ex p s) where
  fmap f = Ex . rmap f . runEx

instance Cosieve p r => Cosieve (Ex p) r where
  cosieve = cosieve . runEx

instance Corepresentable p => Corepresentable (Ex p) where
  type Corep (Ex p) = Corep p
  cotabulate = Ex . cotabulate

instance (Profunctor p, Distributive (p s)) => Distributive (Ex p s) where
  distribute = Ex . distribute . fmap runEx
  collect f = Ex . collect (runEx . f)

instance (Distributive (p s), Corepresentable p) => Representable (Ex p s) where
  type Rep (Ex p s) = Corep p s
  tabulate = cotabulate
  index = cosieve
