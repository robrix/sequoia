{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Functor.Value
( -- * Values
  Value
, V(..)
, Representable(..)
  -- * Construction
, inV0
, inV
, idV
  -- * Elimination
, (∘)
  -- * Coercion
, _V
  -- * Computation
, (>∘∘<)
, (>∘∘∘<)
, (<∘∘>)
  -- * Ambient environment
, Env(..)
, val
) where

import Control.Applicative (liftA2)
import Data.Functor.Rep
import Sequoia.Conjunction
import Sequoia.Disjunction
import Sequoia.Optic.Iso
import Sequoia.Profunctor.Value (Env(..), V(..), val)

-- Values

class Representable v => Value v


-- Construction

inV0 :: Representable v => a -> v a
inV0 = inV . const

inV :: Representable v => (Rep v -> a) -> v a
inV = tabulate

inV2 :: Representable v => ((Rep v -> a) -> (Rep v -> b) -> (Rep v -> c)) -> (v a -> v b -> v c)
inV2 f a b = inV (exV a `f` exV b)

idV :: Representable v => v (Rep v)
idV = inV id


-- Elimination

exV, (∘) :: Representable v => v a -> (Rep v -> a)
exV = index
(∘) = index

infixr 8 ∘


-- Coercion

_V :: (Representable v, Representable v') => Iso (v a) (v' a') (Rep v -> a) (Rep v' -> a')
_V = exV <-> inV


-- Computation

(>∘∘<) :: (Conj d, Representable v) => v b -> v c -> v (b `d` c)
(>∘∘<) = inV2 (>---<)

infix 3 >∘∘<

(>∘∘∘<) :: (Conj d, Representable v) => (a -> v b) -> (a -> v c) -> (a -> v (b `d` c))
(>∘∘∘<) = liftA2 (>∘∘<)

infix 3 >∘∘∘<


(<∘∘>) :: (Disj d, Representable v) => (v a -> r) -> (v b -> r) -> (v (a `d` b) -> Rep v -> r)
(l <∘∘> r) ab = (l <--> r) . bitraverseDisjV ab

infix 3 <∘∘>

bitraverseDisjV :: (Disj d, Representable v) => v (a `d` b) -> Rep v -> v a `d` v b
bitraverseDisjV = fmap (bimapDisj inV0 inV0) . (∘)
