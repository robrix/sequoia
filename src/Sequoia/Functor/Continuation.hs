{-# LANGUAGE FunctionalDependencies #-}
-- | Continuations encoded as (contravariant) functors.
module Sequoia.Functor.Continuation
( -- * Continuation functor
  type (•)(..)
  -- * Continuation abstraction
, Continuation(..)
  -- * Construction
, idK
, constK
) where

import Data.Functor.Contravariant

-- Continuation functor

newtype r • a = K { runK :: a -> r }

instance Contravariant ((•) r) where
  contramap f = K . (. f) . runK

instance Continuation r ((•) r) where
  inK = K
  (•) = runK


-- Continuation abstraction

class Contravariant k => Continuation r k | k -> r where
  inK :: (a -> r) -> k a
  (•) :: k a -> (a -> r)

  infixl 7 •


-- Construction

idK :: Continuation r k => k r
idK = inK id

constK :: Continuation r k => r -> k a
constK = inK . const
