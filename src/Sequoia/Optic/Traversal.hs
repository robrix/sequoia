module Sequoia.Optic.Traversal
( -- * Traversals
  Traversal
  -- * Elimination
, traverseOf
) where

import Data.Profunctor
import Data.Profunctor.Traversing
import Sequoia.Optic.Optic

-- Traversals

type Traversal s t a b = forall p . Traversing p => Optic p s t a b


-- Elimination

traverseOf :: Applicative f => Traversal s t a b -> ((a -> f b) -> (s -> f t))
traverseOf o = runStar . o . Star
