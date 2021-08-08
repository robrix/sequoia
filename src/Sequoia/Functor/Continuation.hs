{-# LANGUAGE FunctionalDependencies #-}
-- | Continuations encoded as (contravariant) functors.
module Sequoia.Functor.Continuation
( -- * Continuation functor
  type (•)(..)
  -- * Continuation abstraction
, Continuation(..)
) where

-- Continuation functor

newtype r • a = K { runK :: a -> r }


-- Continuation abstraction

class Continuation r k | k -> r where
  inK :: (a -> r) -> k a
  (•) :: k a -> (a -> r)
