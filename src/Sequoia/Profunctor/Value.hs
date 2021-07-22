{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Value
( -- * Value profunctor
  V(..)
  -- * Construction
, inV0
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
import Control.Category (Category)
import Control.Monad (join)
import Data.Distributive
import Data.Functor.Identity
import Data.Functor.Rep as Co
import Data.Profunctor
import Data.Profunctor.Rep as Pro
import Data.Profunctor.Sieve
import Data.Profunctor.Traversing
import Sequoia.Conjunction
import Sequoia.Disjunction
import Sequoia.Optic.Iso
import Sequoia.Profunctor.Recall

-- Value profunctor

newtype V e a = V { (∘) :: e -> a }
  deriving (Applicative, Category, Choice, Closed, Cochoice, Pro.Corepresentable, Costrong, Env e, Functor, Mapping, Monad, Profunctor, Co.Representable, Pro.Representable, Strong, Traversing)

instance Distributive (V e) where
  distribute = distributeRep
  collect = collectRep

instance Sieve V Identity where
  sieve = rmap Identity . (∘)

instance Cosieve V Identity where
  cosieve = lmap runIdentity . (∘)


-- Construction

inV0 :: a -> V e a
inV0 = pure

idV :: V e e
idV = V id


-- Coercion

_V :: Iso (V e a) (V e' a') (e -> a) (e' -> a')
_V = coerced


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
bitraverseDisjV = fmap (bimapDisj pure pure) . (∘)


-- Ambient environment

class Env e c | c -> e where
  env :: (e -> c) -> c

instance Env e (e -> a) where
  env = join

deriving instance Env e (Forget r e b)
deriving instance Env e (Recall e a b)

val :: Env e c => (a -> c) -> (V e a -> c)
val f v = env (f . (v ∘))
