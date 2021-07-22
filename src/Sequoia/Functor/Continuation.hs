{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Functor.Continuation
( -- * Continuations
  Continuation
, Contravariant(..)
  -- ** Construction
, inK
  -- ** Elimination
, (•)
  -- ** Coercion
, _K
  -- ** Category
, idK
  -- ** Composition
, (<••>)
, (<•••>)
  -- * Ambient control
, Res(..)
, cont
, (••)
, Res1(..)
, cont1
, Res2(..)
) where

import Control.Applicative (liftA2)
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Rep
import Sequoia.Disjunction
import Sequoia.Functor.K
import Sequoia.Optic.Iso
import Sequoia.Profunctor.Recall

-- Continuations

class Representable k => Continuation r k | k -> r

instance Continuation r (K r)


-- Construction

inK :: Representable k => (a -> Rep k) -> k a
inK = tabulate

inK2 :: ((a -> r) -> (b -> r) -> (c -> r)) -> (K r a -> K r b -> K r c)
inK2 f a b = K (runK a `f` runK b)


-- Elimination

(•) :: Representable k => k a -> (a -> Rep k)
(•) = index

infixl 7 •


-- Coercion

_K :: Iso (K r a) (K r' a') (a -> r) (a' -> r')
_K = from contratabulated


-- Category

idK :: K r r
idK = inK id


-- Composition

(<••>) :: Disj d => K r a -> K r b -> K r (a `d` b)
(<••>) = inK2 (<-->)

infix 3 <••>


(<•••>) :: Disj d => (e -> K r a) -> (e -> K r b) -> (e -> K r (a `d` b))
(<•••>) = liftA2 (<••>)

infix 3 <•••>


-- Ambient control

class Res c where
  res :: r -> c e r
  liftRes :: ((c e r -> r) -> c e r) -> c e r

instance Res (->) where
  res = pure
  liftRes f = f =<< flip ($)

instance Res (Recall e) where
  res = Recall . pure
  liftRes f = Recall (\ e -> runRecall (f (`runRecall` e)) e)

cont :: Res c => (((a -> c e r) -> K r a) -> c e r) -> c e r
cont = liftRes . contN

(••) :: (Res c, Representable k) => k a -> a -> c e (Rep k)
k •• v = res (k • v)

infix 7 ••


class Res1 c where
  res1 :: r -> c e r a
  liftRes1 :: ((c e r a -> r) -> c e r a) -> c e r a

cont1 :: Res1 c => (((a -> c e r a) -> K r a) -> c e r a) -> c e r a
cont1 = liftRes1 . contN


class Res2 c where
  res2 :: r -> c e r a b
  liftRes2 :: ((c e r a b -> r) -> c e r a b) -> c e r a b


contN :: (((a -> c) -> K r a) -> c) -> ((c -> r) -> c)
contN f run = f (inK . (run .))
