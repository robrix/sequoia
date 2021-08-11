module Sequoia.DeBruijn.Typed
( -- * Typed de Bruijn indices
  Index(getIndex)
, indexToLevel
  -- * Typed de Bruijn levels
, Level(getLevel)
, levelToIndex
) where

import Data.Functor.Classes

-- Typed de Bruijn indices

-- | De Bruijn indices, counting up from the binding site to the reference site (“inside out”).
newtype Index a as = Index { getIndex :: Int }
  deriving (Eq, Ord)

instance Show (Index a as) where
  showsPrec p = showsUnaryWith showsPrec "Index" p . getIndex


indexToLevel :: Int -> Index a as -> Level a as
indexToLevel cardinality (Index index) = Level $ cardinality - index - 1


-- Typed de Bruijn levels

-- | De Bruijn indices, counting up from the root to the binding site (“outside in”).
newtype Level a as = Level { getLevel :: Int }
  deriving (Eq, Ord)

instance Show (Level a as) where
  showsPrec p = showsUnaryWith showsPrec "Level" p . getLevel

levelToIndex :: Int -> Level a as -> Index a as
levelToIndex cardinality (Level level) = Index $ cardinality - level - 1
