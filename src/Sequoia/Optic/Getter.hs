module Sequoia.Optic.Getter
( -- * Getters
  Getter
) where

import Data.Profunctor
import Sequoia.Bijection

-- Getters

type Getter s t a b = forall p . (Cochoice p, Strong p) => Optic p s t a b
