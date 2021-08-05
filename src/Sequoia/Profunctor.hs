module Sequoia.Profunctor
( -- * Profunctors
  module Data.Profunctor
  -- * Composition
, (^>>)
) where

import Data.Profunctor

(^>>) :: Profunctor p => (a' -> a) -> (a `p` b) -> (a' `p` b)
(^>>) = lmap

infixr 1 ^>>
