module Sequoia.Optic.Getter
( -- * Getters
  Getter
  -- * Construction
, to
  -- * Elimination
, view
) where

import Data.Profunctor
import Sequoia.Bicontravariant
import Sequoia.Bijection

-- Getters

type Getter s a = forall p . (Bicontravariant p, Profunctor p) => Optic' p s a


-- Construction

to :: (s -> a) -> Getter s a
to f = lmap f . rphantom


-- Elimination

view :: Optic (Forget a) s t a b -> (s -> a)
view = (`views` id)
