module Sequoia.Print.Doc
( -- * Documents
  Doc(..)
) where

import Data.Monoid (Endo(..))
import Sequoia.Print.Class

-- Documents

newtype Doc = Doc { getDoc :: ShowS }
  deriving (Monoid, Semigroup) via Endo String

instance Show Doc where
  showsPrec _ = getDoc

instance Document Doc where
  char c = Doc (c:)
  string s = Doc (s<>)
