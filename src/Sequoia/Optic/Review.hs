module Sequoia.Optic.Review
( -- * Reviews
  Review
, Review'
  -- * Construction
, unto
) where

import Data.Bifunctor
import Data.Profunctor
import Sequoia.Bicontravariant (lphantom)
import Sequoia.Bijection

-- Reviews

type Review s t a b = forall p . (Bifunctor p, Profunctor p) => Optic p s t a b

type Review' s a = forall p . (Bifunctor p, Profunctor p) => Optic p s s a a


-- Construction

unto :: (b -> t) -> Review s t a b
unto f = lphantom . rmap f
