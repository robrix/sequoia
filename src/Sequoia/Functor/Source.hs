module Sequoia.Functor.Source
( -- * Sources
  Src(..)
) where

import Sequoia.Functor.K
import Sequoia.Profunctor.Context

-- Sources

newtype Src e r b = Src { runSrc :: K r b -> C e r }
