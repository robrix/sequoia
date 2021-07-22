module Sequoia.Connective.ForAll
( -- * Universal quantification
  ForAll(..)
) where

import Sequoia.Functor.Continuation
import Sequoia.Polarity

-- Universal quantification

newtype ForAll r p f = ForAll { runForAll :: forall x . Polarized p x => K r (K r (f x)) }

instance Polarized N (ForAll r p f)
