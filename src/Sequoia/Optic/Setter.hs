module Sequoia.Optic.Setter
( -- * Setters
  Setter
, sets
, set
) where

import Data.Profunctor.Mapping
import Sequoia.Bijection

-- Setters

type Setter s t a b = forall p . Mapping p => Optic p s t a b

sets :: ((a -> b) -> (s -> t)) -> Setter s t a b
sets = roam

set :: Setter s t a b -> b -> s -> t
set o = over o . const
