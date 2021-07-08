module Sequoia.Connective.ForAll
( -- * Universal quantification
  ForAll(..)
) where

import Sequoia.Continuation
import Sequoia.Polarity

-- Universal quantification

newtype ForAll k p f = ForAll { runForAll :: forall x . Polarized p x => k **f x }

instance Polarized N (ForAll k p f)
