module Sequoia.Bicontravariant
( -- * Bicontravariant functors
  Bicontravariant(..)
) where

-- Bicontravariant functors

class Bicontravariant p where
  contrabimap :: (a' -> a) -> (b' -> b) -> a `p` b -> a' `p` b'
