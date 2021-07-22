{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Functor.Continuation
( -- * Continuations
  Continuation
, K(..)
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
) where

import Control.Applicative (liftA2)
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Adjunction
import Data.Functor.Contravariant.Rep
import Data.Functor.Identity
import Sequoia.Confunctor
import Sequoia.Disjunction
import Sequoia.Functor.Applicative
import Sequoia.Optic.Iso
import Sequoia.Profunctor.Continuation (Res(..))

-- Continuations

class Representable k => Continuation r k | k -> r


newtype K r a = K { runK :: a -> r }
  deriving (Monoid, Semigroup)
  deriving (Contravariant) via Flip (->) r
  deriving (Confunctor, Contrachoice, Contraclosed, Contracochoice, Contracosieve Identity, Contracostrong, Contracorepresentable, Contrarepresentable, Contrasieve Identity, Contrastrong) via Flip (->)

instance Representable (K r) where
  type Rep (K r) = r
  tabulate = K
  index = runK

instance Adjunction (K r) (K r) where
  leftAdjunct  f a = K ((`runK` a) . f)
  rightAdjunct f b = K ((`runK` b) . f)

instance Contrapply (K r) where
  contraliftA2 f (K a) (K b) = K (either a b . f)
  contrap (K a) (K b) = K (either a b)

instance Contrapplicative (K r)

instance Continuation r (K r)


-- Construction

inK :: Representable k => (a -> Rep k) -> k a
inK = tabulate


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
a <••> b = K (runK a <--> runK b)

infix 3 <••>


(<•••>) :: Disj d => (e -> K r a) -> (e -> K r b) -> (e -> K r (a `d` b))
(<•••>) = liftA2 (<••>)

infix 3 <•••>


-- Ambient control

cont :: Res r c => (((a -> c) -> K r a) -> c) -> c
cont f = liftRes (\ run -> f (inK . (run .)))

(••) :: (Res (Rep k) c, Representable k) => k a -> a -> c
k •• v = res (k • v)

infix 7 ••
