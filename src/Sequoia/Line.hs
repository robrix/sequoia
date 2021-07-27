module Sequoia.Line
( -- * Lines
  Line(..)
, nullLine
  -- * Line endings
, LineEnding(..)
) where

import qualified Sequoia.List as List
import           Sequoia.Span

-- Lines

data Line = Line { lineSpan :: Span, lineContents :: List.List Char, lineEnding :: Maybe LineEnding }
  deriving (Eq, Ord, Show)

nullLine :: Line -> Bool
nullLine = (&&) <$> null . lineContents <*> null . lineEnding


-- Line endings

data LineEnding
  = CR
  | LF
  | CRLF
  deriving (Bounded, Enum, Eq, Ord, Show)
