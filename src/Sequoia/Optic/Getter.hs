{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Optic.Getter
( -- * Getters
  Getter
, IsGetter
  -- * Construction
, to
  -- * Elimination
, view
) where

import Data.Profunctor
import Sequoia.Bicontravariant
import Sequoia.Bijection

-- Getters

type Getter s a = forall p . IsGetter p => Optic' p s a

class    (Bicontravariant p, Profunctor p) => IsGetter p
instance (Bicontravariant p, Profunctor p) => IsGetter p


-- Construction

to :: (s -> a) -> Getter s a
to f = lmap f . rphantom


-- Elimination

view :: Optic (Forget a) s t a b -> (s -> a)
view = (`views` id)
