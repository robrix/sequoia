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

-- Lines

data Line = Line { lineContents :: List.List Char, lineEnding :: Maybe LineEnding }
  deriving (Eq, Ord, Show)


-- Construction

fromChar :: Char -> Line
fromChar c = Line (List.singleton c) nl
  where
  nl = case c of
    '\r' -> Just CR
    '\n' -> Just LF
    _    -> Nothing


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
