module Sequoia.Optic.Getter
( -- * Getters
  Getter
, view
) where

import Data.Profunctor
import Sequoia.Bijection

-- Getters

type Getter s t a b = forall p . (Cochoice p, Strong p) => Optic p s t a b

view :: Optic (Forget a) s t a b -> (s -> a)
view = (`views` id)
