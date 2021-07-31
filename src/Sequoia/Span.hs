module Sequoia.Span
( -- * Source positions
  Pos(..)
, line_
, col_
  -- * Source spans
, Span(..)
, start_
, end_
) where

import Fresnel.Lens

-- Source positions

data Pos = Pos { line :: {-# UNPACK #-} !Int, col :: {-# UNPACK #-} !Int }
  deriving (Eq, Ord, Show)

line_, col_ :: Lens' Pos Int

line_ = lens line (\ p line -> p{ line })
col_  = lens col  (\ p col  -> p{ col  })


-- Source spans

data Span = Span { start :: {-# UNPACK #-} !Pos, end :: {-# UNPACK #-} !Pos }
  deriving (Eq, Ord, Show)

instance Semigroup Span where
  Span s1 e1 <> Span s2 e2 = Span (min s1 s2) (max e1 e2)


start_, end_ :: Lens' Span Pos

start_ = lens start (\ p start -> p{ start })
end_   = lens end   (\ p end   -> p{ end   })
