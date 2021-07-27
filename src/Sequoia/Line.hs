module Sequoia.Line
( -- * Lines
  Line(..)
  -- * Elimination
, nullLine
  -- * Line endings
, LineEnding(..)
) where

import qualified Sequoia.Cons as List

-- Lines

data Line = Line { lineContents :: List.List Char, lineEnding :: Maybe LineEnding }
  deriving (Eq, Ord, Show)


-- Elimination

nullLine :: Line -> Bool
nullLine = (&&) <$> null . lineContents <*> null . lineEnding


-- Line endings

data LineEnding
  = CR
  | LF
  | CRLF
  deriving (Bounded, Enum, Eq, Ord, Show)

instance Semigroup LineEnding where
  CR <> LF = CRLF
  LF <> CR = CRLF
  a  <> b  = max a b
