module Sequoia.Connective.ForAll
( -- * Universal quantification
  ForAll(..)
) where

import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Universal quantification

newtype ForAll r p f = ForAll { runForAll :: forall x . Polarized p x => f x • r • r }

instance Polarized N (ForAll r p f)
