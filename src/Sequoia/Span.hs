module Sequoia.Span
( -- * Source positions
  Pos(..)
  -- * Source spans
, Span(..)
) where

-- Source positions

data Pos = Pos { line :: {-# UNPACK #-} !Int, col :: {-# UNPACK #-} !Int }
  deriving (Eq, Ord, Show)


-- Source spans

data Span = Span { start :: {-# UNPACK #-} !Pos, end :: {-# UNPACK #-} !Pos }
  deriving (Eq, Ord, Show)

instance Semigroup Span where
  Span s1 e1 <> Span s2 e2 = Span (min s1 s2) (max e1 e2)
