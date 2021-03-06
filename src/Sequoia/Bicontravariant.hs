module Sequoia.Bicontravariant
( -- * Bicontravariant functors
  Bicontravariant(..)
, contrafirst
, contrasecond
  -- * Coercion
, biphantom
, lphantom
, rphantom
, bivacuous
, firstvacuous
, secondvacuous
, contravacuous
, contrabivacuous
, contrafirstvacuous
, contrasecondvacuous
, divacuous
, lvacuous
, rvacuous
) where

import Data.Bifunctor
import Data.Functor.Contravariant
import Data.Profunctor
import Data.Void

-- Bicontravariant functors

class Bicontravariant p where
  contrabimap :: (a' -> a) -> (b' -> b) -> a `p` b -> a' `p` b'

instance Bicontravariant (Forget r) where
  contrabimap f _ = Forget . lmap f . runForget

contrafirst  :: Bicontravariant p => (a' -> a) -> a `p` b -> a' `p` b
contrafirst  = (`contrabimap` id)

contrasecond :: Bicontravariant p => (b' -> b) -> a `p` b -> a `p` b'
contrasecond = (id `contrabimap`)


-- Coercion

biphantom :: (Bifunctor p, Bicontravariant p) => p a b -> p c d
biphantom = bivacuous . contrabivacuous

lphantom :: (Profunctor p, Bifunctor p) => p a b -> p c b
lphantom = firstvacuous . lvacuous

rphantom :: (Profunctor p, Bicontravariant p) => p a b -> p a c
rphantom = rvacuous . contrasecondvacuous

bivacuous :: Bifunctor p => p Void Void -> p a b
bivacuous = bimap absurd absurd

firstvacuous :: Bifunctor p => p Void b -> p a b
firstvacuous = first absurd

secondvacuous :: Bifunctor p => p a Void -> p a b
secondvacuous = second absurd

contravacuous :: Contravariant f => f a -> f Void
contravacuous = contramap absurd

contrabivacuous :: Bicontravariant p => p a b -> p Void Void
contrabivacuous = contrabimap absurd absurd

contrafirstvacuous :: Bicontravariant p => p a b -> p Void b
contrafirstvacuous = contrafirst absurd

contrasecondvacuous :: Bicontravariant p => p a b -> p a Void
contrasecondvacuous = contrasecond absurd

divacuous :: Profunctor p => p a Void -> p Void b
divacuous = dimap absurd absurd

lvacuous :: Profunctor p => p a b -> p Void b
lvacuous = lmap absurd

rvacuous :: Profunctor p => p a Void -> p a b
rvacuous = rmap absurd
