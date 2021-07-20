module Sequoia.Optic.Traversal
( -- * Traversals
  Traversal
) where

import Data.Profunctor.Traversing
import Sequoia.Optic.Optic

-- Traversals

type Traversal s t a b = forall p . Traversing p => Optic p s t a b
