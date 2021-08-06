module Sequoia.Bifunctor.Join
( Join(..)
) where

import Data.Bifunctor
import Data.Functor.Contravariant
import Sequoia.Bicontravariant

newtype Join p a = Join { runJoin :: p a a }

instance Bifunctor p => Functor (Join p) where
  fmap f = Join . bimap f f . runJoin

instance Bicontravariant p => Contravariant (Join p) where
  contramap f = Join . contrabimap f f . runJoin
