module Sequoia.Optic.Review
( -- * Reviews
  Review
, Review'
) where

import Data.Bifunctor
import Data.Profunctor
import Sequoia.Bijection

-- Reviews

type Review s t a b = forall p . (Bifunctor p, Profunctor p) => Optic p s t a b

type Review' s a = forall p . (Bifunctor p, Profunctor p) => Optic p s s a a
