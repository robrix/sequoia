module Sequoia.Profunctor
( -- * Profunctors
  module Data.Profunctor
  -- * Composition
, (^>>)
, (<<^)
, (>>^)
, (^<<)
) where

import Data.Profunctor

(^>>) :: Profunctor p => (a' -> a) -> (a `p` b) -> (a' `p` b)
(^>>) = lmap

(<<^) :: Profunctor p => (a `p` b) -> (a' -> a) -> (a' `p` b)
(<<^) = flip lmap

infixr 1 ^>>, <<^

(>>^) :: Profunctor p => (a `p` b) -> (b -> b') -> (a `p` b')
(>>^) = flip rmap

(^<<) :: Profunctor p => (b -> b') -> (a `p` b) -> (a `p` b')
(^<<) = rmap

infixr 1 >>^, ^<<
