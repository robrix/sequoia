module Sequoia.Optic.Review
( Review
) where

import Data.Bifunctor
import Data.Profunctor
import Sequoia.Bijection

-- Reviews

type Review s t a b = forall p . (Bifunctor p, Profunctor p) => Optic p s t a b
