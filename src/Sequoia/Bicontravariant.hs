module Sequoia.Bicontravariant
( -- * Bicontravariant functors
  Bicontravariant(..)
, contrafirst
) where

-- Bicontravariant functors

class Bicontravariant p where
  contrabimap :: (a' -> a) -> (b' -> b) -> a `p` b -> a' `p` b'

contrafirst :: Bicontravariant p => (a' -> a) -> a `p` b -> a' `p` b
contrafirst = (`contrabimap` id)
