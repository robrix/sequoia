module Sequoia.DeBruijn.Typed
( -- * Typed de Bruijn indices
  Index(getIndex)
, indexToLevel
  -- * Typed de Bruijn levels
, Level(getLevel)
, levelToIndex
) where

import Sequoia.Context
