-- | Continuations encoded as (contravariant) functors.
module Sequoia.Functor.Continuation
( -- * Continuation functor
  type (•)(..)
) where

-- Continuation functor

newtype r • a = K { runK :: a -> r }
