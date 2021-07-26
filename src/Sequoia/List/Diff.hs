module Sequoia.List.Diff
( -- * Difference lists
  List(..)
) where

import Data.Monoid (Endo(..))

-- Difference lists

newtype List a = List (Endo [a])
