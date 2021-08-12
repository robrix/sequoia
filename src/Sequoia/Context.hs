{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
module Sequoia.Context
( -- * Empty contexts
  ΓΔ(..)
  -- * Context extensions
, type (<)(..)
, type (>)(..)
  -- * Typed de Bruijn indices
, IxL(..)
, IxR(..)
, Index(getIndex)
, indexToLevel
  -- * Typed de Bruijn levels
, Level(getLevel)
, levelToIndex
  -- * Context abstractions
, Ctx(..)
, Cardinality(..)
) where

import Data.Functor.Classes
import Sequoia.Profunctor.Continuation

-- Empty contexts

newtype ΓΔ e r = ΓΔ { getΓΔ :: e }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)


-- Context extensions

data a < b = a :< b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 4 <, :<

data as > a = as :> (a • R as)

infixl 4 >, :>


-- Typed de Bruijn indices

data IxL a as where
  IxLZ :: IxL a (a < b)
  IxLS :: IxL c b -> IxL c (a < b)

deriving instance Show (IxL as a)

data IxR as a where
  IxRZ :: IxR (a > b) b
  IxRS :: IxR a c -> IxR (a > b) c

deriving instance Show (IxR as a)


-- | De Bruijn indices, counting up from the binding site to the reference site (“inside out”).
newtype Index a as = Index { getIndex :: Int }
  deriving (Eq, Ord)

instance Show (Index a as) where
  showsPrec p = showsUnaryWith showsPrec "Index" p . getIndex


indexToLevel :: Cardinality as => Index a as -> Level a as
indexToLevel i@(Index index) = Level $ cardinality i - index - 1


-- Typed de Bruijn levels

-- | De Bruijn indices, counting up from the root to the binding site (“outside in”).
newtype Level a as = Level { getLevel :: Int }
  deriving (Eq, Ord)

instance Show (Level a as) where
  showsPrec p = showsUnaryWith showsPrec "Level" p . getLevel


levelToIndex :: Cardinality as => Level a as -> Index a as
levelToIndex l@(Level level) = Index $ cardinality l - level - 1


-- Context abstractions

class Ctx c where
  type E c
  type R c

  getE :: c -> E c

  (<!) :: IxL a c -> c -> a

  infixr 2 <!

  (!>) :: c -> IxR c a -> (a • R c)

  infixl 2 !>

instance Ctx (ΓΔ e r) where
  type E (ΓΔ e r) = e
  type R (ΓΔ e r) = r
  getE = getΓΔ
  i <! _ = case i of {}
  _ !> i = case i of {}

instance Ctx as => Ctx (a < as) where
  type E (a < as) = E as
  type R (a < as) = R as
  getE (_ :< t) = getE t
  IxLZ   <! h :< _ = h
  IxLS i <! _ :< t = i <! t
  _ !> i = case i of {}

instance Ctx as => Ctx (as > a) where
  type E (as > a) = E as
  type R (as > a) = R as
  getE (i :> _) = getE i
  _  :> a !> IxRZ   = a
  as :> _ !> IxRS i = as !> i
  i <! _ :> _ = case i of {}


class Cardinality ctx where
  cardinality :: i ctx -> Int

instance Cardinality (ΓΔ e r) where
  cardinality _ = 0

instance Cardinality as => Cardinality (a < as) where
  cardinality c = 1 + cardinality (tailOf c)

tailOf :: i (a < as) -> [as]
tailOf _ = []

instance Cardinality as => Cardinality (as > a) where
  cardinality c = 1 + cardinality (initOf c)

initOf :: i (as > a) -> [as]
initOf _ = []
