module Sequoia.List.Diff
( -- * Difference lists
  List(..)
  -- * Elimination
, runList
) where

import Data.Monoid (Endo(..))

-- Difference lists

newtype List a = List (Endo [a])
  deriving (Monoid, Semigroup)


-- Elimination

runList :: List a -> [a]
runList (List l) = appEndo l []
