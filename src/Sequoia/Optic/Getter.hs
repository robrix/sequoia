{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Optic.Getter
( -- * Getters
  Getter
, Getter'
, IsGetter
  -- * Construction
, to
  -- * Elimination
, views
, view
, (~>)
) where

import Control.Effect.Reader
import Data.Profunctor
import Sequoia.Bicontravariant
import Sequoia.Bijection

-- Getters

type Getter s t a b = forall p . IsGetter p => Optic p s t a b

type Getter' s a = forall p . IsGetter p => Optic' p s a

class    (Bicontravariant p, Profunctor p) => IsGetter p
instance (Bicontravariant p, Profunctor p) => IsGetter p


-- Construction

to :: (s -> a) -> Getter s t a b
to f = lmap f . rphantom


-- Elimination

views :: Has (Reader s) sig m => Getter s t a b -> (a -> r) -> m r
views b = asks . runForget . b . Forget

view :: Has (Reader s) sig m => Getter s t a b -> m a
view = (`views` id)

(~>) :: s -> Getter s t a b -> a
s ~> o = view o s

infixl 8 ~>
