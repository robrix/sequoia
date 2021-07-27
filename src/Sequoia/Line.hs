module Sequoia.Line
( -- * Lines
  Line(..)
  -- * Construction
, fromChar
  -- * Elimination
, nullLine
  -- * Line endings
, LineEnding(..)
) where

import qualified Sequoia.Cons as List
import           Sequoia.Span

-- Lines

data Line = Line { lineSpan :: Span, lineContents :: List.List Char, lineEnding :: Maybe LineEnding }
  deriving (Eq, Ord, Show)


-- Construction

fromChar :: Char -> Line
fromChar c = Line span (List.singleton c) nl
  where
  (span, nl) = case c of
    '\r' -> (Span (Pos 0 0) (Pos 1 0), Just CR)
    '\n' -> (Span (Pos 0 0) (Pos 1 0), Just LF)
    _    -> (Span (Pos 0 0) (Pos 0 1), Nothing)


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
