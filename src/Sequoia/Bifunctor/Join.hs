module Sequoia.Bifunctor.Join
( Join(..)
) where

import Data.Bifoldable
import Data.Bifunctor
import Data.Functor.Contravariant
import Sequoia.Bicontravariant

newtype Join p a = Join { runJoin :: p a a }

instance Bifoldable p => Foldable (Join p) where
  foldMap f = bifoldMap f f . runJoin

instance Bifunctor p => Functor (Join p) where
  fmap f = Join . bimap f f . runJoin

instance Bicontravariant p => Contravariant (Join p) where
  contramap f = Join . contrabimap f f . runJoin
