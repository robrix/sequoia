module Sequoia.Optic.Getter
( -- * Getters
  Getter
, view
) where

import Data.Profunctor
import Sequoia.Bijection

-- Getters

type Getter s a = forall p . (Cochoice p, Strong p) => Optic' p s a

view :: Optic (Forget a) s t a b -> (s -> a)
view = (`views` id)
