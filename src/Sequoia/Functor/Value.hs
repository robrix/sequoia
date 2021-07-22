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

idV :: Representable v => v (Rep v)
idV = inV id


-- Elimination

exV :: Representable v => v a -> (Rep v -> a)
exV = index


-- Coercion

_V :: (Representable v, Representable v') => Iso (v a) (v' a') (Rep v -> a) (Rep v' -> a')
_V = exV <-> inV


-- Computation

(>∘∘<) :: Conj d => V e b -> V e c -> V e (b `d` c)
a >∘∘< b = V ((a ∘) >---< (b ∘))

infix 3 >∘∘<

(>∘∘∘<) :: Conj d => (a -> V e b) -> (a -> V e c) -> (a -> V e (b `d` c))
(>∘∘∘<) = liftA2 (>∘∘<)

infix 3 >∘∘∘<


(<∘∘>) :: Disj d => (V e a -> r) -> (V e b -> r) -> (V e (a `d` b) -> e -> r)
(l <∘∘> r) ab = (l <--> r) . bitraverseDisjV ab

infix 3 <∘∘>

bitraverseDisjV :: Disj d => V e (a `d` b) -> e -> V e a `d` V e b
bitraverseDisjV = fmap (bimapDisj inV0 inV0) . (∘)
