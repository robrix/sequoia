module Sequoia.Profunctor.Sum
( (:+:)(..)
) where

import Control.Arrow ((+++))
import Data.Profunctor

newtype (p :+: q) a b = Sum { runSum :: Either (p a b) (q a b) }

infixr 5 :+:

instance (Profunctor p, Profunctor q) => Profunctor (p :+: q) where
  dimap f g = Sum . (dimap f g +++ dimap f g) . runSum

instance (Strong p, Strong q) => Strong (p :+: q) where
  first'  = Sum . (first'  +++ first' ) . runSum
  second' = Sum . (second' +++ second') . runSum

instance (Costrong p, Costrong q) => Costrong (p :+: q) where
  unfirst  = Sum . (unfirst  +++ unfirst ) . runSum
  unsecond = Sum . (unsecond +++ unsecond) . runSum
