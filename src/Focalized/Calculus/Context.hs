{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Calculus.Context
( -- * Γ
  Γ(..)
, type (<)(..)
, (<|)
  -- * Δ
, Δ
, absurdΔ
, type (>)(..)
, (|>)
  -- * Mixfix syntax
, type (|-)
, type (-|)
  -- * Membership
, mkV
, type (:.)(..)
, ContextL(..)
, replaceL
, ContextR(..)
, replaceR
, MemberΓ(..)
, replaceΓ
, MemberΔ(..)
, replaceΔ
) where

import Control.Applicative (liftA2)
import Control.Monad (ap)
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Coerce (coerce)
import Data.Distributive
import Data.Functor.Adjunction
import Data.Functor.Contravariant
import Data.Functor.Identity
import Data.Functor.Rep
import Focalized.CPS
import Focalized.Conjunction
import Focalized.Disjunction

-- Γ

data Γ = Γ

data a < b = a :< b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 4 <, :<, <|

instance Conj (<) where
  (-><-) = (:<)
  exl (a :< _) = a
  exr (_ :< b) = b

instance Bifoldable (<) where
  bifoldMap = bifoldMapConj

instance Bifunctor (<) where
  bimap = bimapConj

instance Bitraversable (<) where
  bitraverse = bitraverseConj

(<|) :: i -> is -> i < is
(<|) = (-><-)


-- Δ

data Δ

absurdΔ :: Δ -> a
absurdΔ = \case


data a > b
  = L a
  | R b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixl 4 >, |>

instance Disj (>) where
  inl = L
  inr = R
  f <--> g = \case
    L a -> f a
    R b -> g b

instance Bifoldable (>) where
  bifoldMap = bifoldMapDisj

instance Bifunctor (>) where
  bimap = bimapDisj

instance Bitraversable (>) where
  bitraverse = bitraverseDisj

instance Applicative ((>) a) where
  pure = R
  (<*>) = ap

instance Monad ((>) a) where
  (>>=) = flip (inl <-->)

-- | Discrimination of continuations in '>'.
--
-- @¬A ✕ ¬B -> ¬(A + V)@
(|>) :: r •os -> r •o -> r •(os > o)
(|>) = liftK2 (<-->)


-- Mixfix syntax

type l -| r = r l
type l |- r = l r

infixl 2 |-, -|


-- Membership

-- | Convenience to construct a named variable given the same name available for use inside. This can obviate the need for @-XScopedTypeVariables@ in some situations which would otherwise require them.
mkV :: (n :. () -> a) -> n :. a
mkV f = V (f (V ()))

newtype (n :: k) :. a = V { getV :: a }
  deriving (Functor)
  deriving (Applicative, Monad, Representable) via Identity

infixr 5 :.

instance Distributive ((:.) n) where
  distribute = V . fmap getV

instance Adjunction ((:.) n) ((:.) n) where
  unit   = coerce
  counit = coerce

  leftAdjunct  = coerce
  rightAdjunct = coerce


class ContextL (n :: k) a as as' | as a -> as', as as' -> a, as n -> a where
  {-# MINIMAL ((selectL, dropL) | removeL), insertL #-}
  selectL :: n :. as -> n :. a
  selectL = fmap exl . removeL
  dropL :: n :. as -> n :. as'
  dropL = fmap exr . removeL
  removeL :: n :. as -> n :. (a, as')
  removeL = liftA2 (,) <$> selectL <*> dropL
  insertL :: n :. (a, as') -> n :. as

instance ContextL n a (n :. a < as) as where
  selectL = fmap (getV . exl)
  dropL = fmap exr
  removeL = liftA2 (-><-) <$> fmap (getV . exl) <*> fmap exr
  insertL = fmap (uncurry ((<|) . V))

instance ContextL n a as as' => ContextL n a (n' :. b < as) (n' :. b < as') where
  selectL = selectL . fmap exr
  dropL = fmap . (<|) <$> exl . getV <*> dropL . fmap exr
  removeL = fmap . fmap . (<|) <$> exl . getV <*> removeL . fmap exr
  insertL = fmap . (<|) <$> exl . exr . getV <*> insertL . fmap (fmap exr)

replaceL :: (ContextL n a as as', ContextL n b bs as') => (a -> b) -> (n :. as -> n :. bs)
replaceL f = insertL . fmap (first f) . removeL


class ContextR (n :: k) a as as' | as a -> as', as as' -> a, as n -> a where
  {-# MINIMAL ((selectR, dropR) | removeR), insertR #-}
  selectR :: n :. r •as -> n :. r •a
  selectR = fmap exr . removeR
  dropR :: n :. r •as -> n :. r •as'
  dropR = fmap exl . removeR
  removeR :: n :. r •as -> n :. (r •as', r •a)
  removeR = liftA2 (,) <$> dropR <*> selectR
  insertR :: n :. (r •as', r •a) -> n :. r•as

instance ContextR n a (as > n :. a) as where
  selectR = fmap (contramap (inr . V))
  dropR = fmap (contramap inl)
  removeR = fmap ((,) <$> contramap inl <*> contramap (inr . V))
  insertR = fmap (uncurry (|>) . fmap (contramap getV))

instance ContextR n a as as' => ContextR n a (as > n' :. b) (as' > n' :. b) where
  selectR = selectR . fmap (contramap inl)
  dropR = dropR +•+ id
  removeR v = (,) <$> dropR v <*> selectR v
  insertR = insertR . fmap (first (contramap inl)) |•| fmap (contramap inr . exl)

replaceR :: (ContextR n a as as', ContextR n b bs as') => (a -> b) -> (n :. r• bs -> n :. r•as)
replaceR f = insertR . fmap (fmap (contramap f)) . removeR


class ConcatΓ as bs cs | as bs -> cs, as cs -> bs, bs cs -> as where
  concatΓ :: as -> bs -> cs

instance ConcatΓ as Γ as where
  concatΓ = const

instance ConcatΓ as bs cs => ConcatΓ (a < as) bs (a < cs) where
  concatΓ (a :< as) bs = a :< concatΓ as bs


class ConcatΔ as bs cs | as bs -> cs, as cs -> bs, bs cs -> as where
  concatΔ :: r •as -> r •bs -> r •cs

instance ConcatΔ as Δ as where
  concatΔ = const

instance ConcatΔ as bs cs => ConcatΔ (as > a) bs (cs > a) where
  concatΔ as bs = concatΔ (contramap inl as) bs |> contramap inr as


class MemberΓ n a as as' | n a as -> as', as as' -> n a where
  injectΓ :: n :. (a, as') -> n :. as
  rejectΓ :: n :. as -> n :. (a, as')

instance MemberΓ n a (n :. a < as) as where
  injectΓ = liftA2 (<|) <$> fmap (V . exl) <*> fmap exr
  rejectΓ = liftA2 (,) <$> fmap (getV . exl) <*> fmap exr

instance MemberΓ n a as as' => MemberΓ n a (n' :. b < as) (n' :. b < as') where
  injectΓ = liftA2 (<|) <$> fmap (exl . exr) <*> injectΓ . fmap (fmap exr)
  rejectΓ = rightAdjunct (\ (b :< as) -> leftAdjunct (fmap (fmap (b <|)) . rejectΓ) as)

replaceΓ :: (MemberΓ n a as as', MemberΓ n b bs as') => (a -> b) -> (n :. as -> n :. bs)
replaceΓ f = injectΓ . fmap (first f) . rejectΓ


class MemberΔ n a as as' | n a as -> as', as as' -> n a where
  injectΔ :: n :. (r •as', r •a) -> n :. r •as
  rejectΔ :: n :. r •as -> n :. (r •as', r •a)

instance MemberΔ n a (as > n :. a) as where
  injectΔ = liftA2 (|>) <$> fmap exl <*> fmap (contramap getV . exr)
  rejectΔ = liftA2 (,) <$> fmap (contramap inl) <*> fmap (contramap (inr . V))

instance MemberΔ n a as as' => MemberΔ n a (as > n' :. b) (as' > n' :. b) where
  injectΔ = liftA2 (|>) <$> injectΔ . fmap (first (contramap inl)) <*> fmap (contramap inr . exl)
  rejectΔ = rightAdjunct (\ as -> leftAdjunct (fmap (first (|> contramap inr as)) . rejectΔ) (contramap inl as))

replaceΔ :: (MemberΔ n a as as', MemberΔ n b bs as') => (b -> a) -> (n :. r •as -> n :. r •bs)
replaceΔ f = injectΔ . fmap (fmap (contramap f)) . rejectΔ
