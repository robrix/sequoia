{-# LANGUAGE TypeFamilies #-}
module Sequoia.Bifunctor.Join
( Join(..)
) where

import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Distributive
import Data.Functor.Contravariant
import Data.Functor.Rep
import Sequoia.Bicontravariant
import Sequoia.Bidistributive
import Sequoia.Birepresentable

newtype Join p a = Join { runJoin :: p a a }

instance Bifoldable p => Foldable (Join p) where
  foldMap f = bifoldMap f f . runJoin

instance Bifunctor p => Functor (Join p) where
  fmap f = Join . bimap f f . runJoin

instance Bicontravariant p => Contravariant (Join p) where
  contramap f = Join . contrabimap f f . runJoin

instance Bitraversable p => Traversable (Join p) where
  traverse f = fmap Join . bitraverse f f . runJoin

instance Bidistributive p => Distributive (Join p) where
  distribute g = Join (bidistribute (runJoin <$> g))
  collect f g = Join (bicollect (runJoin . f) g)

instance Birepresentable p => Representable (Join p) where
  type Rep (Join p) = Birep p
  tabulate f = Join (bitabulate f f)
  index = biindex . runJoin
