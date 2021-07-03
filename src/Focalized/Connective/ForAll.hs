module Focalized.Connective.ForAll
( -- * Universal quantification
  ForAll(..)
) where

import Focalized.Continuation
import Focalized.Polarity

-- Universal quantification

newtype ForAll r p f = ForAll { runForAll :: forall x . Polarized p x => r ••f x }

instance Polarized N (ForAll r p f)
