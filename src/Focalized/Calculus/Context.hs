{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
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
, ContextR(..)
) where

import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Distributive
import Data.Functor.Adjunction
import Data.Functor.Identity
import Data.Functor.Rep
import Focalized.CPS
import Focalized.Conjunction
import Focalized.Disjunction
import GHC.Base

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

newtype (n :: Symbol) :. a = V { getV :: a }
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


class ContextL (n :: Symbol) a as as' | as a -> as', as as' -> a, as n -> a where
  {-# MINIMAL ((selectL, dropL) | removeL), insertL #-}
  selectL :: n :. as -> n :. a
  selectL = fmap exl . removeL
  dropL :: n :. as -> n :. as'
  dropL = fmap exr . removeL
  removeL :: n :. as -> n :. (a, as')
  removeL = liftA2 (,) <$> selectL <*> dropL
  insertL :: n :. (a, as') -> n :. as
  replaceL :: (ContextL n' b bs bs', n ~ n', bs' ~ as') => (a -> b) -> (n :. as -> n :. bs)
  replaceL f = insertL . fmap (first f) . removeL

instance {-# OVERLAPPING #-} ContextL n a (n :. a < as) as where
  selectL = fmap (getV . exl)
  dropL = fmap exr
  removeL = liftA2 (-><-) <$> fmap (getV . exl) <*> fmap exr
  insertL = fmap (uncurry ((<|) . V))

instance {-# OVERLAPPING #-} ContextL n a as as' => ContextL n a (n' :. b < as) (n' :. b < as') where
  selectL = selectL . fmap exr
  dropL = fmap . (<|) <$> exl . getV <*> dropL . fmap exr
  removeL = fmap . fmap . (<|) <$> exl . getV <*> removeL . fmap exr
  insertL = fmap . (<|) <$> exl . exr . getV <*> insertL . fmap (fmap exr)


class ContextR (n :: Symbol) a as as' | as a -> as', as as' -> a, as n -> a where
  selectR :: n :. as -> n :. Maybe a
  selectR = fmap exrD . removeR
  dropR :: n :. as -> n :. Maybe as'
  dropR = fmap exlD . removeR
  removeR :: n :. as -> n :. Either as' a
  insertR :: n :. Either as' a -> n :. as
  replaceR :: (ContextR n b bs bs', bs' ~ as') => (a -> b) -> (n :. as -> n :. bs)
  replaceR f = insertR . fmap (fmap f) . removeR

instance {-# OVERLAPPING #-} ContextR n a (as > n :. a) as where
  selectR = fmap (fmap getV . exrD)
  dropR = fmap exlD
  removeR = fmap (inl <--> inr . getV)
  insertR = fmap (fmap V . (inl <--> inr))

instance {-# OVERLAPPING #-} ContextR n a as as' => ContextR n a (as > n' :. b) (as' > n' :. b) where
  selectR = selectR -||- const (pure Nothing)
  dropR = fmap (fmap inl) . dropR -||- fmap (Just . inr)
  removeR = fmap (first inl) . removeR -||- fmap (inl . inr)
  insertR = (fmap inl . insertR . fmap inl -||- fmap inr) -||- fmap inl . insertR . fmap inr
