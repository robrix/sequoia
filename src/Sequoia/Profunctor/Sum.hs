module Sequoia.Profunctor.Sum
( (:+:)(..)
) where

import Control.Arrow ((+++))
import Data.Profunctor

newtype (p :+: q) a b = Sum { runSum :: Either (p a b) (q a b) }

infixr 5 :+:

instance (Profunctor p, Profunctor q) => Profunctor (p :+: q) where
  dimap f g = Sum . (dimap f g +++ dimap f g) . runSum
