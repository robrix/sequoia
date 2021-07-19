module Sequoia.Bicontravariant
( -- * Bicontravariant functors
  Bicontravariant(..)
, contrafirst
, contrasecond
  -- * Coercion
, biphantom
, lphantom
, rphantom
, contrabivacuous
) where

import Data.Bifunctor
import Data.Profunctor
import Data.Void

-- Bicontravariant functors

class Bicontravariant p where
  contrabimap :: (a' -> a) -> (b' -> b) -> a `p` b -> a' `p` b'

contrafirst  :: Bicontravariant p => (a' -> a) -> a `p` b -> a' `p` b
contrafirst  = (`contrabimap` id)

contrasecond :: Bicontravariant p => (b' -> b) -> a `p` b -> a `p` b'
contrasecond = (id `contrabimap`)


-- Coercion

biphantom :: (Bifunctor p, Bicontravariant p) => p a b -> p c d
biphantom = bimap absurd absurd . contrabimap absurd absurd

lphantom :: (Profunctor p, Bifunctor p) => p a b -> p c b
lphantom = first absurd . lmap absurd

rphantom :: (Profunctor p, Bicontravariant p) => p a b -> p a c
rphantom = rmap absurd . contrasecond absurd

contrabivacuous :: Bicontravariant p => p a b -> p Void Void
contrabivacuous = contrabimap absurd absurd
