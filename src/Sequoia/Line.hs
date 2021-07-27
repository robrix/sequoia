module Sequoia.Line
( -- * Lines
  Line(..)
, LineEnding(..)
, nullLine
) where

import qualified Sequoia.List as List
import           Sequoia.Span

-- Lines

data Line = Line { lineSpan :: Span, lineContents :: List.List Char, lineEnding :: Maybe LineEnding }
  deriving (Eq, Ord, Show)

data LineEnding
  = CR
  | LF
  | CRLF
  deriving (Bounded, Enum, Eq, Ord, Show)

nullLine :: Line -> Bool
nullLine = (&&) <$> null . lineContents <*> null . lineEnding
